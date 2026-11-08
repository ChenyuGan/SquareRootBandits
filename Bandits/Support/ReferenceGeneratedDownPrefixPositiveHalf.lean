/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownPrefixEvent
public import Bandits.Support.ReferenceGeneratedDownBatchBankBridge
public import Bandits.Support.ReferenceGeneratedAffineHashHalf

import Lean.Elab.Tactic.Omega

/-!
# Physical generated DOWN prefix events and their affine hash half

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-138`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42,74-124`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The source events below retain the actual generated launch branch, D's
physical prefix marker, the original pair-remainder cylinder, and the current
physical DOWN decoder test. The affine half identity is then transported from
the actual current test to A's source-generated event on the unchanged full
source law. This is one-round support for the fresh-reset DOWN source-law
recurrence after calendar acceptance; it does not prove that recurrence, a
tail bound, or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open scoped Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceGeneratedDownPrefixEvent
open Bandits.Support.ReferenceGeneratedAffineHashHalf

namespace Bandits.Support.ReferenceGeneratedDownPrefixPositiveHalf

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceGeneratedDownBatchCalendar.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev Candidate (p : Parameters) :=
  AffineChannelLaw.Word (AffineBatchDecoder.width p)

variable {p : Parameters} {rate : RateInput p}

open ReferenceGeneratedDownBatchCalendar
open ReferenceGeneratedDownPrefixEvent
open ReferenceGeneratedAffineHashHalf

/-- A genuine generated DOWN launch branch with the original row selector,
the elapsed launch, and the selected follower retained in its source proof. -/
abbrev GeneratedDownBranch
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (i : Fin (p.m - 1))
    (s : ℕ) :=
  {source : SourceInput p // source ∈
    ReferenceGeneratedAffineHashHalf.generatedLaunchBranch (rate := rate)
      rewards C_star C_h j r (0, i) s}

/-- The actual next physical DOWN input on the generated launch branch. -/
def generatedCurrentDownInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (i : Fin (p.m - 1))
    (s : ℕ) (hs : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (z : GeneratedDownBranch (rate := rate) rewards C_star C_h j r i s) :
    ReferenceActivePhysicalStep.RoundInput p rate :=
  ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch (rate := rate)
    rewards C_star C_h j r (0, i) s hs control0 z

/-- The literal one-step record at the actual generated next input. Its output
is the accepted physical step, with no separately supplied trace. -/
def generatedCurrentDownRecord
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (i : Fin (p.m - 1))
    (s : ℕ) (hs : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (z : GeneratedDownBranch (rate := rate) rewards C_star C_h j r i s) :
    ReferenceFollowerDownDecoderReplay.Record p rate :=
  ⟨generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hs control0 z,
    ReferenceActivePhysicalStep.step
      (generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hs control0 z),
    rfl⟩

/-- The branch's actual channel selector is the same focal follower used by
the physical DOWN positive test. -/
theorem generatedCurrentDown_senderIndex
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (i : Fin (p.m - 1))
    (s : ℕ) (hs : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (z : GeneratedDownBranch (rate := rate) rewards C_star C_h j r i s) :
    ReferenceActivePhysicalStep.upSenderIndex
      (generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hs control0 z) = i := by
  let x := generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hs control0 z
  have hfields := ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch_original_fields
    (rate := rate) rewards C_star C_h j r (0, i) s hs control0 z
  have hselector :=
    (ReferenceSelectedAffinePairLaw.selector_eq_iff p j r (0, i) z.1).mp z.2.1
  have hselected : x.selected = j := by
    calc
      x.selected = ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.1 :=
        hfields.2.1
      _ = ActualInitializationPhysicalStep.selectedRowIndex p z.1 := by
        rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      _ = j := by
        have h := congrArg Prod.fst z.2.1
        change ActualInitializationPhysicalStep.selectedRowIndex p z.1 = j at h
        exact h
  have htime : x.time = r := hfields.2.2.1
  have hrows : x.rows = (z.1).1.2 := by
    change (ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch
      (rate := rate) rewards C_star C_h j r (0, i) s hs control0 z).rows = (z.1).1.2
    exact hfields.1
  have hslice : (x.row.2 x.time).1 = (((z.1).1.2 j).2 r).1 := by
    change ((x.rows x.selected).2 x.time).1 = (((z.1).1.2 j).2 r).1
    rw [hrows, hselected, htime]
  have hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p ((x.row.2 x.time).1) =
      some ((0, i) : ContinuousLearningRows.Channel p) := by
    change ReferenceSelectedAffinePairLaw.selectedChannel p
      (((x.rows x.selected).2 x.time).1) = _
    rw [hrows, hselected, htime]
    exact hselector.2
  have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      ((x.row.2 x.time).1) = i := by
    have hchannel' : ReferenceSelectedAffinePairLaw.channelFromDraws p
        (PublicDiscreteDraws.slotDraw ((x.row.2 x.time).1),
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            ((x.row.2 x.time).1)) =
        some ((0, i) : ContinuousLearningRows.Channel p) := by
      simpa only [ReferenceSelectedAffinePairLaw.selectedChannel] using hchannel
    by_cases hdown : PublicDiscreteDraws.slotDraw ((x.row.2 x.time).1) =
        PublicDiscreteDraws.downSlot
    · have hpair : (((0 : Fin 2), PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          ((x.row.2 x.time).1)) : ContinuousLearningRows.Channel p) = (0, i) := by
        have hchannel'' := hchannel'
        rw [ReferenceSelectedAffinePairLaw.channelFromDraws, if_pos hdown] at hchannel''
        exact Option.some.inj hchannel''
      simpa [PublicDiscreteDraws.followerCount, ContinuousLearningRows.d] using
        congrArg Prod.snd hpair
    · by_cases hup : PublicDiscreteDraws.slotDraw ((x.row.2 x.time).1) =
          PublicDiscreteDraws.upSlot
      · have hpair : (((1 : Fin 2), PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            ((x.row.2 x.time).1)) : ContinuousLearningRows.Channel p) = (0, i) := by
          have hchannel'' := hchannel'
          rw [ReferenceSelectedAffinePairLaw.channelFromDraws, if_neg hdown,
            if_pos hup] at hchannel''
          exact Option.some.inj hchannel''
        have hfirst := congrArg Prod.fst hpair
        norm_num at hfirst
      · simp [ReferenceSelectedAffinePairLaw.channelFromDraws, hdown, hup] at hchannel'
  rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw x]
  exact hdraw

private theorem recordLogged_of_downCallGate
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1))
    (hgate : ReferenceActiveAffinePositiveTest.downCallGate
      (record.output.preparation.followers.followers i)
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) = true) :
    ∃ state memory logged,
      (record.output.preparation.followers.followers i).configuration = .ordinary state memory ∧
      ActiveFollowerLogging.checkedLogging i
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).activation
        (record.output.preparation.followers.followers i).time
        ((record.output.preparation.followers.followers i).arm,
          record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .ok logged ∧
      (record.output.followers i).downInput = some logged := by
  classical
  let prepared := record.output.preparation
  let follower := prepared.followers.followers i
  let own := prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hgate' := hgate
  change ReferenceActiveAffinePositiveTest.downCallGate follower own = true at hgate'
  cases hconfiguration : follower.configuration with
  | dagger =>
      simp [prepared, follower, own, ReferenceActiveAffinePositiveTest.downCallGate,
        hconfiguration] at hgate'
  | ordinary state memory =>
      by_cases hstatus : state.status = .unoccupied
      · simp only [ReferenceActiveAffinePositiveTest.downCallGate, hconfiguration,
          hstatus, if_pos] at hgate'
        cases hlogging : ActiveFollowerLogging.checkedLogging follower.follower follower.row
            follower.activation follower.time (follower.arm, own) state with
        | error failure => simp [hlogging] at hgate'
        | ok logged =>
            have halign := prepared.follower_alignment i
            have hlogging' := hlogging
            rw [halign.2.1] at hlogging'
            refine ⟨state, memory, logged, ?_, ?_, ?_⟩
            · simpa [prepared, follower] using hconfiguration
            · change ActiveFollowerLogging.checkedLogging i
                (record.output.preparation.followers.followers i).row
                (record.output.preparation.followers.followers i).activation
                (record.output.preparation.followers.followers i).time
                ((record.output.preparation.followers.followers i).arm,
                  record.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .ok logged
              simpa [prepared, follower, own] using hlogging'
            · rw [← ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics
                record i]
              change (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
                follower own).downInput = some logged
              let recorded := ReferenceActivePhysicalStep.recordFollower
                prepared.coordinator.downView follower.follower follower.row follower.activation
                follower.time follower.active follower.arm own state
              have hrecordInput : recorded.downInput = some logged := by
                simp [recorded, ReferenceActivePhysicalStep.recordFollower, hstatus, hlogging]
              unfold ReferenceActivePhysicalStep.finishFollower
              simp only [hconfiguration]
              cases hresult : recorded.result with
              | error failure => simp [recorded, hrecordInput, hresult]
              | ok post =>
                  cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate follower.follower
                      follower.row follower.time own state memory post <;>
                    simp [recorded, hrecordInput, hresult, hfinish]
      · simp [prepared, follower, own, ReferenceActiveAffinePositiveTest.downCallGate,
          hconfiguration, hstatus] at hgate'

/-- The literal D test on an actual one-step record agrees in both directions
with P's selected positive test. The theorem pins its time, original focal
sample, and option-valued sent word, and does not require an ordinary
successor or any later completion. -/
theorem executedTestOfRound_iff_downPositive
    (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1))
    (hselected : ReferenceActivePhysicalStep.upSenderIndex record.input = i) :
    ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
        some ⟨record.input.time, (record.input.row.2 record.input.time).2 (0, i),
          ReferenceActiveAffinePositiveTest.downSent record.input⟩ ↔
      ReferenceActiveAffinePositiveTest.downPositive record.input = true := by
  classical
  constructor
  · intro htest
    let round := ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i
    let diagnostic := round.2.2.2
    cases hcallCode : round.2.2.1 with
    | none => simp [ReferenceGeneratedDownBatchCalendar.executedTestOfRound,
        round, diagnostic, hcallCode] at htest
    | some callCode =>
      cases hcutCode : diagnostic.2.2 with
      | none => simp [ReferenceGeneratedDownBatchCalendar.executedTestOfRound,
          round, diagnostic, hcallCode, hcutCode] at htest
      | some cutFields =>
        have htestExpanded := htest
        simp [ReferenceGeneratedDownBatchCalendar.executedTestOfRound,
          round, diagnostic, hcallCode, hcutCode] at htestExpanded
        have hcondition := htestExpanded.1
        have hdiagnostics :=
          ReferenceGeneratedDownBatchBankBridge.roundDownObservation_diagnostics_eq_actual record i
        have hcutDiagnostic := hcutCode
        change (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          record.input i).2.2.2.2.2 = some cutFields at hcutDiagnostic
        rw [hdiagnostics] at hcutDiagnostic
        have hcutWitness : ∃ cut,
            (record.output.followers i).down = some cut ∧
              ReferenceDownCompletedAmbiguityMeasurability.cutFields cut = cutFields := by
          cases hdown : (record.output.followers i).down with
          | none => simp [hdown] at hcutDiagnostic
          | some cut =>
            have hc : ReferenceDownCompletedAmbiguityMeasurability.cutFields cut = cutFields := by
              simpa [hdown] using hcutDiagnostic
            exact ⟨cut, rfl, hc⟩
        obtain ⟨cut, hactualCut, hcutFields⟩ := hcutWitness
        have hcomparison : cut.rawComparison.isSome = true := by
          have hproj := congrArg
            (fun fields : ReferenceDownCompletedAmbiguityMeasurability.DownCutFields p =>
              fields.2.2.1.isSome) hcutFields
          have hproj' : cut.rawComparison.isSome = cutFields.2.2.1.isSome := by
            simpa [ReferenceDownCompletedAmbiguityMeasurability.cutFields] using hproj
          rw [hproj']
          exact hcondition.2
        have hpositive :
            0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val := by
          have hgrid :
              0 < (ActualInitializationPhysicalStep.observationOfGrid p
                (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i)).val.val := by
            simpa [round, ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation] using
              hcondition.1
          have hown : ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i =
              ActualInitializationPhysicalStep.observationOfGrid p
                (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i) := by
            have hgrid' := congrFun (ReferenceActiveHorizonMeasurability.roundRecordCode_front
              record).2.2.2 (PublicDiscreteDraws.followerPlayer p.two_le_m i)
            change ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i =
              record.gridFeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) at hgrid'
            rw [hgrid']
            exact record.output.preparation.feedback.observations_eq _
          rw [hown]
          exact hgrid
        have hcall : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
            some callCode := by
          change ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation
            record.input i = some callCode
          change ReferenceDownCompletedAmbiguityMeasurability.roundCallObservation
            record.input i = some callCode at hcallCode
          exact hcallCode
        have hdiagnosticCall : ReferenceActiveAffinePositiveTest.downDiagnosticCall
            (record.output.followers i) = true := by
          simp [ReferenceActiveAffinePositiveTest.downDiagnosticCall, hactualCut, hcomparison]
        have hownBool : decide (0 <
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val) = true := by
          exact decide_eq_true hpositive
        have hgate : ReferenceActiveAffinePositiveTest.downCallGate
            (record.output.preparation.followers.followers i)
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) = true := by
          have hdiag := hdiagnosticCall
          rw [← ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics
            record i] at hdiag
          change ReferenceActiveAffinePositiveTest.downDiagnosticCall
            (ReferenceActivePhysicalStep.finishFollower
              record.output.preparation.coordinator.downView
              (record.output.preparation.followers.followers i)
              (record.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))) = true at hdiag
          exact (ReferenceActiveAffinePositiveTest.finishFollower_down_call _ _ _).symm.trans hdiag
        obtain ⟨state, memory, logged, hconfiguration, hlogging, hlogged⟩ :=
          recordLogged_of_downCallGate record i hgate
        have hbridge := ReferenceGeneratedDownBatchBankBridge.executedTestOfRound_eq_actual
          record i callCode logged cut hcall hlogged hactualCut hcomparison hpositive
        rcases hbridge with ⟨_, _, _, _⟩
        have hrecordPositive := ReferenceActiveAffinePositiveTest.record_downPositive record
        rw [hselected, hdiagnosticCall, hownBool] at hrecordPositive
        exact hrecordPositive
  · intro hpositive
    have hrecordPositive := ReferenceActiveAffinePositiveTest.record_downPositive record
    rw [hselected] at hrecordPositive
    have hdiagnosticPositive :
        ReferenceActiveAffinePositiveTest.downDiagnosticCall (record.output.followers i) &&
          decide (0 < (record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val) = true := by
      exact hrecordPositive ▸ hpositive
    have hparts := Bool.and_eq_true_iff.mp hdiagnosticPositive
    rcases hparts with ⟨hdiagnosticCall, hown⟩
    cases hdown : (record.output.followers i).down with
    | none => simp [ReferenceActiveAffinePositiveTest.downDiagnosticCall, hdown] at hdiagnosticCall
    | some cut =>
      have hcomparison : cut.rawComparison.isSome = true := by
        simpa [ReferenceActiveAffinePositiveTest.downDiagnosticCall, hdown] using hdiagnosticCall
      have hgate : ReferenceActiveAffinePositiveTest.downCallGate
          (record.output.preparation.followers.followers i)
          (record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) = true := by
        have hdiag := hdiagnosticCall
        rw [← ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics
          record i] at hdiag
        change ReferenceActiveAffinePositiveTest.downDiagnosticCall
          (ReferenceActivePhysicalStep.finishFollower
            record.output.preparation.coordinator.downView
            (record.output.preparation.followers.followers i)
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))) = true at hdiag
        exact (ReferenceActiveAffinePositiveTest.finishFollower_down_call _ _ _).symm.trans hdiag
      obtain ⟨state, memory, logged, hconfiguration, hlogging, hlogged⟩ :=
        recordLogged_of_downCallGate record i hgate
      have hchoice : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
          .ordinary state memory := by
        change (record.output.preparation.followers.followers i).configuration = _
        exact hconfiguration
      have hcallNe : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record ≠ none := by
        intro hnone
        have hd := (ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_eq_none_iff
          i record).mp hnone
        rw [hchoice] at hd
        cases hd
      obtain ⟨callCode, hcall⟩ := Option.ne_none_iff_exists'.mp hcallNe
      have hpositiveOwn :
          0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val := by
        change 0 < (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val
        exact of_decide_eq_true hown
      have hbridge := ReferenceGeneratedDownBatchBankBridge.executedTestOfRound_eq_actual
        record i callCode logged cut hcall hlogged hdown hcomparison hpositiveOwn
      rcases hbridge with ⟨htest, hsent, _, _⟩
      rw [hsent] at htest
      exact htest

/-- The literal generated source event for a physical DOWN positive test:
the original launch selector, D's `[s,r)` marker, the pair-remainder
prefix cylinder, and the actual current record's exact D test are all present
in the event formula. -/
def downPrefixPositiveSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (i : Fin (p.m - 1))
    (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) : Set (SourceInput p) :=
  {source | ∃ branch : GeneratedDownBranch (rate := rate) rewards C_star C_h j r i s,
    branch.1 = source ∧
    ReferenceSelectedAffinePairLaw.selector p r source = (j, some (0, i)) ∧
    ReferenceGeneratedDownPrefixEvent.sourcePrefixMarker rate rewards C_star C_h r s hs hsr
      i alpha halpha halphaR candidate q hq hqQ
      ⟨branch.1, branch.2.2.1, branch.2.2.2⟩ ∧
    (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i) source).2 ∈
      ReferenceGeneratedDownPrefixEvent.prefixPairCylinder rate rewards C_star C_h j r s
        hs hsr control0 i alpha halpha halphaR candidate q hq hqQ ∧
    ∃ test,
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
          (generatedCurrentDownRecord (rate := rate) rewards C_star C_h j r i s hsr control0
            branch).input i) = some test ∧
      test.time = r ∧
      test.sample = (((generatedCurrentDownRecord (rate := rate) rewards C_star C_h j r i s
        hsr control0 branch).input.row).2 r).2 (0, i) ∧
      test.sent = ReferenceActiveAffinePositiveTest.downSent
        (generatedCurrentDownRecord (rate := rate) rewards C_star C_h j r i s hsr control0
          branch).input ∧
      test.sent ≠ some candidate}

/-- Refinement of the literal physical source event by hash one on the
original current pair `(j,r,DOWN,i)`. -/
def downPrefixPositiveHashOneSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (i : Fin (p.m - 1))
    (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) : Set (SourceInput p) :=
  {source | source ∈ downPrefixPositiveSourceEvent (rate := rate) rewards C_star C_h j r s
      hs hsr i alpha halpha halphaR candidate q hq hqQ control0 ∧
    AffineChannelLaw.affineHash (((source.1.2 j).2 r).2 (0, i)) candidate = 1}

private theorem sourcePrefixMarker_iff_prefixPairCylinder
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (i : Fin (p.m - 1))
    (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (branch : GeneratedDownBranch (rate := rate) rewards C_star C_h j r i s) :
    ReferenceGeneratedDownPrefixEvent.sourcePrefixMarker rate rewards C_star C_h r s hs hsr
      i alpha halpha halphaR candidate q hq hqQ
      ⟨branch.1, branch.2.2.1, branch.2.2.2⟩ ↔
    (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i) branch.1).2 ∈
      ReferenceGeneratedDownPrefixEvent.prefixPairCylinder rate rewards C_star C_h j r s
        hs hsr control0 i alpha halpha halphaR candidate q hq hqQ := by
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p branch.1 = j := by
    have h := congrArg Prod.fst branch.2.1
    change ActualInitializationPhysicalStep.selectedRowIndex p branch.1 = j at h
    exact h
  have hstratum : branch.1 ∈ ReferenceGeneratedDownPrefixEvent.sourcePrefixStratum
      rate rewards C_star C_h j s := ⟨hselected, branch.2.2.1, branch.2.2.2⟩
  let launch : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs :=
    ⟨branch.1, branch.2.2.1, branch.2.2.2⟩
  have hprefix : branch.1 ∈ ReferenceGeneratedDownPrefixEvent.sourcePrefixEvent rate rewards
      C_star C_h j r s hs hsr i alpha halpha halphaR candidate q hq hqQ ↔
      (ReferenceSelectedAffinePairLaw.fixedPairSplit p j r (0, i) branch.1).2 ∈
        ReferenceGeneratedDownPrefixEvent.prefixPairCylinder rate rewards C_star C_h j r s
          hs hsr control0 i alpha halpha halphaR candidate q hq hqQ := by
    have h := congrArg (fun S : Set (SourceInput p) => branch.1 ∈ S)
      (ReferenceGeneratedDownPrefixEvent.sourcePrefixEvent_eq_pairCylinder rate rewards
        C_star C_h j r s hs hsr control0 i alpha halpha halphaR candidate q hq hqQ)
    simpa only [Set.mem_preimage] using Iff.of_eq h
  constructor
  · intro hmarker
    have hevent : branch.1 ∈ ReferenceGeneratedDownPrefixEvent.sourcePrefixEvent rate rewards
        C_star C_h j r s hs hsr i alpha halpha halphaR candidate q hq hqQ := by
      exact ⟨hstratum, by simpa [launch] using hmarker⟩
    exact hprefix.mp hevent
  · intro hcylinder
    rcases hprefix.mpr hcylinder with ⟨hbranchStratum, hmarker⟩
    simpa [launch] using hmarker

theorem generatedPositiveSourceEvent_eq_physical
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (i : Fin (p.m - 1))
    (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    downPrefixPositiveSourceEvent (rate := rate) rewards C_star C_h j r s hs hsr i
        alpha halpha halphaR candidate q hq hqQ control0 =
      ReferenceGeneratedAffineHashHalf.generatedPositiveSourceEvent (rate := rate)
        rewards C_star C_h j r 0 i s hsr control0 candidate
        (ReferenceGeneratedDownPrefixEvent.prefixPairCylinder rate rewards C_star C_h j r s
          hs hsr control0 i alpha halpha halphaR candidate q hq hqQ) := by
  classical
  ext source
  constructor
  · rintro ⟨branch, rfl, hselector, hmarker, hcylinder, test, htest, htime, hsample,
      hsent, hneq⟩
    have hsender := generatedCurrentDown_senderIndex (rate := rate) rewards C_star C_h j r i s
      hsr control0 branch
    have hpositive : ReferenceActiveAffinePositiveTest.downPositive
        (generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hsr control0 branch) =
          true := by
      have hfields := ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch_original_fields
        (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 branch
      have htest' :
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
            (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
              (generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hsr control0
                branch) i) =
            some ⟨(generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hsr
                control0 branch).time,
              (((generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hsr
                control0 branch).row).2
                (generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hsr
                  control0 branch).time).2 (0, i),
              ReferenceActiveAffinePositiveTest.downSent
                (generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hsr
                  control0 branch)⟩ := by
          rcases test with ⟨testTime, testSample, testSent⟩
          change testTime = r at htime
          let x := generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hsr control0 branch
          have hr : x.time = r := hfields.2.2.1
          have htime' : testTime = x.time := htime.trans hr.symm
          change testSample = ((x.row.2 r).2 (0, i)) at hsample
          have hsample' : testSample = ((x.row.2 x.time).2 (0, i)) := by
            rw [hr]
            exact hsample
          change testSent = ReferenceActiveAffinePositiveTest.downSent x at hsent
          have htestObject : (⟨testTime, testSample, testSent⟩ :
              ReferenceGeneratedDownBatchCalendar.ExecutedTest p) =
              ⟨x.time, ((x.row.2 x.time).2 (0, i)),
                ReferenceActiveAffinePositiveTest.downSent x⟩ := by
            cases htime'
            cases hsample'
            cases hsent
            rfl
          rw [htestObject] at htest
          exact htest
      have hiff := executedTestOfRound_iff_downPositive (rate := rate)
        (generatedCurrentDownRecord (rate := rate) rewards C_star C_h j r i s hsr control0 branch)
        i hsender
      exact hiff.mp (by simpa [generatedCurrentDownRecord, generatedCurrentDownInput,
        hfields.2.2.1] using htest')
    refine ⟨branch.2, hcylinder, ?_, ?_⟩
    · simpa [ReferenceGeneratedAffineHashHalf.directionPositive, generatedCurrentDownInput] using
        hpositive
    · simpa [ReferenceGeneratedAffineHashHalf.directionSent, generatedCurrentDownInput] using
        hsent ▸ hneq
  · rintro ⟨hbranch, hcylinder, hpositive, hsent⟩
    let branch : GeneratedDownBranch (rate := rate) rewards C_star C_h j r i s := ⟨source, hbranch⟩
    have hmarker := (sourcePrefixMarker_iff_prefixPairCylinder (rate := rate) rewards C_star C_h
      j r s hs hsr i alpha halpha halphaR candidate q hq hqQ control0 branch).2 hcylinder
    have hsender := generatedCurrentDown_senderIndex (rate := rate) rewards C_star C_h j r i s
      hsr control0 branch
    have hfields := ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch_original_fields
      (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 branch
    let x := generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hsr control0 branch
    have htest := (executedTestOfRound_iff_downPositive (rate := rate)
      (generatedCurrentDownRecord (rate := rate) rewards C_star C_h j r i s hsr control0 branch)
      i hsender).mpr (by simpa [ReferenceGeneratedAffineHashHalf.directionPositive,
        generatedCurrentDownRecord, generatedCurrentDownInput, x] using hpositive)
    have htestAtR : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation x i) =
      some ⟨r, ((x.row.2 r).2 (0, i)), ReferenceActiveAffinePositiveTest.downSent x⟩ := by
      simpa [generatedCurrentDownRecord, generatedCurrentDownInput, x,
        hfields.2.2.1] using htest
    refine ⟨branch, rfl, branch.2.1, hmarker, hcylinder, ?_⟩
    refine ⟨⟨r, ((x.row.2 r).2 (0, i)),
      ReferenceActiveAffinePositiveTest.downSent x⟩,
      ?_, rfl, ?_, rfl, ?_⟩
    · simpa [generatedCurrentDownRecord, x, hfields.2.2.1] using htestAtR
    · rfl
    · simpa [ReferenceGeneratedAffineHashHalf.directionSent, x,
        generatedCurrentDownInput] using hsent

/-- The physical hash-one event is exactly A's generated source refinement on
the concrete D prefix-pair cylinder. -/
theorem generatedPositiveHashOneSourceEvent_eq_physical
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (i : Fin (p.m - 1))
    (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    downPrefixPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h j r s hs hsr i
        alpha halpha halphaR candidate q hq hqQ control0 =
      ReferenceGeneratedAffineHashHalf.generatedPositiveHashOneSourceEvent (rate := rate)
        rewards C_star C_h j r 0 i s hsr control0 candidate
        (ReferenceGeneratedDownPrefixEvent.prefixPairCylinder rate rewards C_star C_h j r s
          hs hsr control0 i alpha halpha halphaR candidate q hq hqQ) := by
  ext source
  simp only [downPrefixPositiveHashOneSourceEvent, Set.mem_setOf_eq,
    ReferenceGeneratedAffineHashHalf.generatedPositiveHashOneSourceEvent,
    Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [generatedPositiveSourceEvent_eq_physical (rate := rate) rewards C_star C_h j r s
    hs hsr i alpha halpha halphaR candidate q hq hqQ control0]

/-- Borel measurability of the physical DOWN positive source event, via its
proved equality with A's event on D's concrete prefix-pair cylinder. -/
theorem measurableSet_downPrefixPositiveSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (i : Fin (p.m - 1))
    (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (downPrefixPositiveSourceEvent (rate := rate) rewards C_star C_h j r s
      hs hsr i alpha halpha halphaR candidate q hq hqQ control0) := by
  rw [generatedPositiveSourceEvent_eq_physical (rate := rate) rewards C_star C_h j r s
    hs hsr i alpha halpha halphaR candidate q hq hqQ control0]
  exact ReferenceGeneratedAffineHashHalf.measurableSet_generatedPositiveSourceEvent
    (rate := rate) rewards C_star C_h j r 0 i s hsr control0 candidate
    (ReferenceGeneratedDownPrefixEvent.prefixPairCylinder rate rewards C_star C_h j r s
      hs hsr control0 i alpha halpha halphaR candidate q hq hqQ)
    (ReferenceGeneratedDownPrefixEvent.measurableSet_prefixPairCylinder rate rewards C_star C_h
      j r s hs hsr control0 i alpha halpha halphaR candidate q hq hqQ)

/-- Borel measurability of the physical hash-one refinement. -/
theorem measurableSet_downPrefixPositiveHashOneSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (i : Fin (p.m - 1))
    (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (downPrefixPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h j r s
      hs hsr i alpha halpha halphaR candidate q hq hqQ control0) := by
  rw [generatedPositiveHashOneSourceEvent_eq_physical (rate := rate) rewards C_star C_h j r s
    hs hsr i alpha halpha halphaR candidate q hq hqQ control0]
  exact ReferenceGeneratedAffineHashHalf.measurableSet_generatedPositiveHashOneSourceEvent
    (rate := rate) rewards C_star C_h j r 0 i s hsr control0 candidate
    (ReferenceGeneratedDownPrefixEvent.prefixPairCylinder rate rewards C_star C_h j r s
      hs hsr control0 i alpha halpha halphaR candidate q hq hqQ)
    (ReferenceGeneratedDownPrefixEvent.measurableSet_prefixPairCylinder rate rewards C_star C_h
      j r s hs hsr control0 i alpha halpha halphaR candidate q hq hqQ)

/-- Exact original-law half identity for the actual generated DOWN positive
prefix event, with all original rows, J, rewards, and private coordinates in
the ambient source law. -/
theorem downPrefixPositive_hash_half
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (i : Fin (p.m - 1))
    (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (downPrefixPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h j r s
          hs hsr i alpha halpha halphaR candidate q hq hqQ control0) =
      ((1 : ℝ≥0∞) / 2) *
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (downPrefixPositiveSourceEvent (rate := rate) rewards C_star C_h j r s
            hs hsr i alpha halpha halphaR candidate q hq hqQ control0) := by
  rw [generatedPositiveHashOneSourceEvent_eq_physical (rate := rate) rewards C_star C_h j r s
    hs hsr i alpha halpha halphaR candidate q hq hqQ control0,
    generatedPositiveSourceEvent_eq_physical (rate := rate) rewards C_star C_h j r s
      hs hsr i alpha halpha halphaR candidate q hq hqQ control0]
  exact ReferenceGeneratedAffineHashHalf.downGeneratedPositive_hash_half
    (rate := rate) rewards C_star C_h j r i s hsr control0 candidate
    (ReferenceGeneratedDownPrefixEvent.prefixPairCylinder rate rewards C_star C_h j r s
      hs hsr control0 i alpha halpha halphaR candidate q hq hqQ)
    (ReferenceGeneratedDownPrefixEvent.measurableSet_prefixPairCylinder rate rewards C_star C_h
      j r s hs hsr control0 i alpha halpha halphaR candidate q hq hqQ)

/-- Diagnostic consumer form for the fresh-reset DOWN source-law recurrence
and tail after qth-calendar acceptance: the current entry remains the original
D `ExecutedTest.good` predicate. -/
theorem downPrefixPositiveHashOneSourceEvent_current_good
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (i : Fin (p.m - 1))
    (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (candidate : Candidate p) (q : ℕ) (hq : 1 ≤ q)
    (hqQ : q ≤ AffineBatchDecoder.quota p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (source : SourceInput p)
    (hsource : source ∈ downPrefixPositiveHashOneSourceEvent (rate := rate)
      rewards C_star C_h j r s hs hsr i alpha halpha halphaR candidate q hq hqQ control0) :
    ∃ branch : GeneratedDownBranch (rate := rate) rewards C_star C_h j r i s,
      branch.1 = source ∧ ∃ test,
        ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
            (generatedCurrentDownRecord (rate := rate) rewards C_star C_h j r i s hsr
              control0 branch).input i) = some test ∧
        ReferenceGeneratedDownBatchCalendar.ExecutedTest.good candidate test := by
  rcases hsource.1 with ⟨branch, hbranchSource, hselector, hmarker, hcylinder,
    test, htest, htime, hsample, hsent, hneq⟩
  refine ⟨branch, hbranchSource, test, htest, ⟨hneq, ?_⟩⟩
  have hhash := hsource.2
  have hfields := ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch_original_fields
    (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 branch
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p branch.1 = j := by
    have h := congrArg Prod.fst branch.2.1
    change ActualInitializationPhysicalStep.selectedRowIndex p branch.1 = j at h
    exact h
  let x := generatedCurrentDownInput (rate := rate) rewards C_star C_h j r i s hsr control0 branch
  have hxselected : x.selected = j := by
    calc
      x.selected = ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p branch.1 :=
        hfields.2.1
      _ = ActualInitializationPhysicalStep.selectedRowIndex p branch.1 := by
        rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      _ = j := hselected
  have hrows : x.rows = (branch.1).1.2 := by
    change (ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch
      (rate := rate) rewards C_star C_h j r (0, i) s hsr control0 branch).rows =
        (branch.1).1.2
    exact hfields.1
  have hsampleOriginal : test.sample = (((branch.1).1.2 j).2 r).2 (0, i) := by
    have hsampleX := hsample
    change test.sample = ((x.rows x.selected).2 r).2 (0, i) at hsampleX
    rw [hrows, hxselected] at hsampleX
    exact hsampleX
  have hhash' : AffineChannelLaw.affineHash ((((branch.1).1.2 j).2 r).2 (0, i)) candidate = 1 := by
    rw [hbranchSource]
    exact hhash
  rw [← hsampleOriginal] at hhash'
  exact hhash'

end Bandits.Support.ReferenceGeneratedDownPrefixPositiveHalf

end
