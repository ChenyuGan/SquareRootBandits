/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent
public import Bandits.Support.ReferenceActiveAffinePositiveTest

/-!
# Actual UP prefix events and the positive hash half

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-138`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42,74-124`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The source events here use the actual original-source prefix and the actual
current physical UP diagnostic. They identify that event with the admitted
source-generated UP hash-half event on the concrete prefix cylinder. This is
one-round source-law evidence; it proves no calendar recurrence or regret
theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.AffineChannelLaw
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceGeneratedAffineHashHalf
open Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent
open Bandits.Support.ReferenceActiveAffinePositiveTest

namespace Bandits.Support.ReferenceGeneratedUpPrefixPositiveHalf

abbrev Parameters := ReferenceGeneratedAffineHashHalf.Parameters
abbrev RateInput := ReferenceGeneratedAffineHashHalf.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev PairRemainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (i : Fin (p.m - 1)) :=
  ReferenceGeneratedAffineHashHalf.PairRemainder p q t (1, i)
abbrev UpLaunchSource {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (i : Fin (p.m - 1)) :=
  ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
    (rate := rate) rewards C_star C_h q t s i

variable {p : Parameters} {rate : RateInput p}

/-- The current physical UP input obtained by extending the actual original
source run on `[s,t)` by its next calendar coordinate `t`. -/
def originalSourceCurrentInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    ReferenceActivePhysicalStep.RoundInput p rate := by
  let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  let priorRun := ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s)
    (by omega) input
  exact ReferenceActivePhysicalHorizon.roundInputAt input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s input.property priorRun
    ⟨t.val, ⟨by omega, by omega⟩⟩

/-- The actual current round record, with output tied to the literal physical
step on `originalSourceCurrentInput`. -/
def originalSourceCurrentRecord
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) := by
  let input := originalSourceCurrentInput (rate := rate)
    rewards C_star C_h q t s hs control0 i z
  exact ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩

/-- The constructed current input has the original complete row, selected
private index, physical time, and full reward table. -/
theorem originalSourceCurrentInput_original_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    let x := originalSourceCurrentInput (rate := rate)
      rewards C_star C_h q t s hs control0 i z
    x.rows = z.1.1.2 ∧ x.selected = q ∧ x.time = t ∧ x.rewards = rewards := by
  let x := originalSourceCurrentInput (rate := rate)
    rewards C_star C_h q t s hs control0 i z
  have hindex := ReferenceGeneratedAffineHashHalf.selectedRowIndex_of_generatedLaunchBranch
    (rate := rate) rewards C_star C_h q t (1, i) s z
  dsimp only [x, originalSourceCurrentInput, ReferenceActiveHorizonMeasurability.runOfInput,
    ReferenceActivePhysicalHorizon.roundInputAt,
    ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput]
  exact ⟨rfl, hindex, rfl, rfl⟩

private theorem roundInput_ext
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  simp_all

/-- The current physical input is exactly the input computed by the public
source constructor on the original launch stratum. In particular, its state
is from the same `[s,t)` run, and it restores the original source rows and J. -/
theorem originalSourceCurrentInput_eq_generatedNextInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    originalSourceCurrentInput (rate := rate) rewards C_star C_h q t s hs control0 i z =
      ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch
        (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z := by
  let launch := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
  let control := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1
  let actualLaunch : ReferenceGeneratedUpBatchPrefixEvent.LaunchStart
      (p := p) rate rewards C_star C_h q t s hs control :=
    ⟨launch.1, launch.2.1,
      (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
        rate rewards C_star C_h q t s launch.1 launch.2.1 control0 control).mp launch.2.2⟩
  let factor := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
    rate rewards C_star C_h q t control actualLaunch.1 actualLaunch.2.1 s (t.val - s)
    hs actualLaunch.2.2 (by omega)
  let baselineFactor := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
    rate rewards C_star C_h q t control0 launch.1 launch.2.1 s (t.val - s)
    hs launch.2.2 (by omega)
  have hcommon := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_control_independent
    rate rewards C_star C_h q t launch.1 launch.2.1 control0 s (t.val - s)
    hs (by omega) launch.2.2 control control0
  obtain ⟨active, _, hlaunch, _, hmode, _, hfinal, _⟩ := hcommon
  have hsource : ReferenceGeneratedActivePrefixFactor.splitSource q t control launch.1 = z.1 := by
    have hrem : launch.1 =
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).2 := by
      dsimp [launch]
      exact ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch_val
        (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
    change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      (control, launch.1) = z.1
    dsimp [control]
    rw [hrem]
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm_apply_apply z.1
  have hseed :
      (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
        (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1 = active := by
    have horiginal := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_launch
      (rate := rate) rewards C_star C_h q t s hs control0 i z
    have hlaunchOriginal : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z.1 rewards C_star C_h = some active := by
      simpa [hsource] using hlaunch
    exact Option.some.inj (horiginal.symm.trans hlaunchOriginal)
  have hrun :
      (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega)
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z)).finalState =
        (ReferenceActivePhysicalHorizon.run active z.1.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z.1) rewards s (t.val - s)
          (by omega) hmode).finalState := by
    change (ReferenceActivePhysicalHorizon.run
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
        s (t.val - s) (by omega)
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).property).finalState = _
    cases hseed
    rfl
  have hfinal' : factor.finalState = baselineFactor.finalState := by
    simpa [factor, baselineFactor] using hfinal
  have hstate :
      (originalSourceCurrentInput (rate := rate) rewards C_star C_h q t s hs control0 i z).state =
        (ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch
          (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z).state := by
    rw [ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch_state]
    change (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega)
      (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
        (rate := rate) rewards C_star C_h q t s hs control0 i z)).finalState = baselineFactor.finalState
    calc
      _ = (ReferenceActivePhysicalHorizon.run active z.1.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z.1) rewards s (t.val - s)
          (by omega) hmode).finalState := hrun
      _ = factor.finalState := by
        have hseedFactor := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
          rate rewards C_star C_h q t control launch.1 launch.2.1 s hs actualLaunch.2.2
        have hseedEq :
            ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
              control launch.1 launch.2.1 s hs actualLaunch.2.2 = active :=
          Option.some.inj (hseedFactor.1.symm.trans (by simpa [hsource] using hlaunch))
        have hseedEqActual :
            ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
              control actualLaunch.1 actualLaunch.2.1 s hs actualLaunch.2.2 = active := by
          change ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
              control launch.1 launch.2.1 s hs actualLaunch.2.2 = active
          exact hseedEq
        have hfactorSource : ReferenceGeneratedActivePrefixFactor.splitSource q t control
            actualLaunch.1 = z.1 := by
          change ReferenceGeneratedActivePrefixFactor.splitSource q t control launch.1 = z.1
          exact hsource
        simp only [factor, ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor,
          hfactorSource]
        cases hseedEqActual
        rfl
      _ = baselineFactor.finalState := hfinal'
  have hactual := originalSourceCurrentInput_original_fields
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hgenerated := ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch_original_fields
    (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
  have hindex := ReferenceGeneratedAffineHashHalf.selectedRowIndex_of_generatedLaunchBranch
    (rate := rate) rewards C_star C_h q t (1, i) s z
  apply roundInput_ext hstate
  · exact hactual.1.trans hgenerated.1.symm
  ·
    rw [hactual.2.1, hgenerated.2.1]
    exact hindex.symm.trans
      ((ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
        p z.1).symm.trans hgenerated.2.1.symm)
  · exact hactual.2.2.1.trans hgenerated.2.2.1.symm
  · exact hactual.2.2.2.trans hgenerated.2.2.2.symm

private theorem upTest_condition (i : Fin (p.m - 1))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (test : AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p))
    (htest : ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
      (p := p) (rate := rate) i (some diagnostic) = some test) :
    diagnostic.input.selectedFollower = i ∧
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input) := by
  classical
  have h := htest
  simp only [ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic] at h
  split_ifs at h with hcondition
  · exact hcondition

private theorem upTest_eq_of_both (i : Fin (p.m - 1))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (left right : AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p))
    (hleft : ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
      (p := p) (rate := rate) i (some diagnostic) = some left)
    (hright : ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
      (p := p) (rate := rate) i (some diagnostic) = some right) : left = right := by
  have hl := upTest_condition i diagnostic left hleft
  have hr := upTest_condition i diagnostic right hright
  have hleft' :
      AdaptiveAffineBatchTail.Test.mk diagnostic.input.time.val
        diagnostic.input.affineSample diagnostic.expected = left := by
    have h := hleft
    simpa [ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic, hl.1, hl.2] using h
  have hright' :
      AdaptiveAffineBatchTail.Test.mk diagnostic.input.time.val
        diagnostic.input.affineSample diagnostic.expected = right := by
    have h := hright
    simpa [ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic, hr.1, hr.2] using h
  exact hleft'.symm.trans hright'

private theorem diagnostic_of_upTest (i : Fin (p.m - 1))
    (output : Option (ReferenceActivePhysicalStep.UpDiagnostic p rate))
    (test : AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p))
    (htest : ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
      (p := p) (rate := rate) i output = some test) :
    ∃ diagnostic, output = some diagnostic ∧
      ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
        (p := p) (rate := rate) i (some diagnostic) = some test := by
  cases houtput : output with
  | none => simp [houtput, ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic] at htest
  | some diagnostic => exact ⟨diagnostic, rfl, by simpa [houtput] using htest⟩

/-- On the original UP selector stratum, the actual executed selected-i test
exists exactly when the current physical UP diagnostic is positive. -/
theorem originalSourceCurrentRecord_upTest_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    (ReferenceActiveAffinePositiveTest.upPositive
      (originalSourceCurrentInput (rate := rate) rewards C_star C_h q t s hs control0 i z) = true) ↔
      ∃ test, ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
        (p := p) (rate := rate) i
        (originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z).output.coordinator.up =
          some test := by
  let record := originalSourceCurrentRecord (rate := rate)
    rewards C_star C_h q t s hs control0 i z
  have hselector := (ReferenceSelectedAffinePairLaw.selector_eq_iff
    p q t (1, i) z.1).mp z.2.1
  rcases hselector with ⟨_, hchannel⟩
  have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      ((record.input.rows record.input.selected).2 record.input.time).1 = i := by
    have hfields := originalSourceCurrentInput_original_fields
      (rate := rate) rewards C_star C_h q t s hs control0 i z
    have hdrawSource : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        ((z.1.1.2 q).2 t).1 = i := by
      change ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.1.2 q).2 t).1 = some (1, i) at hchannel
      dsimp [ReferenceSelectedAffinePairLaw.selectedChannel,
        ReferenceSelectedAffinePairLaw.channelFromDraws] at hchannel
      split_ifs at hchannel with hdown hup
      · injection hchannel with hbad
        have hfalse : (0 : Fin 2) ≠ 1 := by decide
        exact (hfalse (congrArg Prod.fst hbad)).elim
      · injection hchannel with hpair
        exact congrArg Prod.snd hpair
    let input := originalSourceCurrentInput (rate := rate)
      rewards C_star C_h q t s hs control0 i z
    change PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      ((input.rows input.selected).2 input.time).1 = i
    rw [hfields.1, hfields.2.1, hfields.2.2.1]
    exact hdrawSource
  have hdiagSelected (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
      (hdiag : record.output.coordinator.up = some diagnostic) :
      diagnostic.input.selectedFollower = i := by
    obtain ⟨_, _, _, _, _, _, hselected, _, _, _, _, _, _⟩ :=
      ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields record diagnostic hdiag
    have hselected' : diagnostic.input.selectedFollower =
        ReferenceActivePhysicalStep.upSenderIndex record.input := by
      simpa [ReferenceActivePhysicalStep.upSenderIndex,
        ReferenceActivePhysicalStep.RoundInput.row] using hselected
    exact hselected'.trans
      ((ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw record.input).trans hdraw)
  change (ReferenceActiveAffinePositiveTest.upPositive record.input = true) ↔ _
  rw [ReferenceActiveAffinePositiveTest.record_upPositive record]
  cases hdiagnostic : record.output.coordinator.up with
  | none =>
      simp [ReferenceActiveAffinePositiveTest.upDiagnosticPositive,
        ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic]
  | some diagnostic =>
      have hselected := hdiagSelected diagnostic hdiagnostic
      constructor
      · intro hpositive
        have heligible : AffineBatchDecoder.eligible
            (CoordinatorUpReception.roundInput diagnostic.input) := by
          simpa [ReferenceActiveAffinePositiveTest.upDiagnosticPositive, hdiagnostic] using hpositive
        exact ⟨⟨diagnostic.input.time.val, diagnostic.input.affineSample, diagnostic.expected⟩,
          by simp [ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic,
            hselected, heligible]⟩
      · rintro ⟨test, htest⟩
        have htest' : ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
            (p := p) (rate := rate) i (some diagnostic) = some test := by
          simpa [record, originalSourceCurrentRecord, hdiagnostic] using htest
        have heligible := (upTest_condition i diagnostic test htest').2
        simp [ReferenceActiveAffinePositiveTest.upDiagnosticPositive, heligible]

/-- The positive test retains the physical time, original focal `(UP,i)`
sample, and actual prepared UP offer, including post-test finish failures. -/
theorem originalSourceCurrentRecord_upPositive_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i)
    (hpositive : ReferenceActiveAffinePositiveTest.upPositive
      (originalSourceCurrentInput (rate := rate) rewards C_star C_h q t s hs control0 i z) = true) :
    ∃ test, ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
        (p := p) (rate := rate) i
        (originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z).output.coordinator.up =
          some test ∧ test.time = t.val ∧
      test.sample = ((z.1.1.2 q).2 t).2 (1, i) ∧
      test.sent = ReferenceActiveAffinePositiveTest.upSent
        (originalSourceCurrentInput (rate := rate) rewards C_star C_h q t s hs control0 i z) := by
  let record := originalSourceCurrentRecord (rate := rate)
    rewards C_star C_h q t s hs control0 i z
  obtain ⟨test, htest⟩ :=
    (originalSourceCurrentRecord_upTest_iff (rate := rate)
      rewards C_star C_h q t s hs control0 i z).mp hpositive
  have htestRecord : ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
      (p := p) (rate := rate) i record.output.coordinator.up = some test := by
    simpa [record, originalSourceCurrentRecord] using htest
  obtain ⟨diagnostic, hdiagnostic, htestCurrent⟩ :=
    diagnostic_of_upTest i record.output.coordinator.up test htestRecord
  have hcondition := upTest_condition i diagnostic test htestCurrent
  have hselectedDiagnostic := hcondition.1
  have heligible := hcondition.2
  have hfields := originalSourceCurrentInput_original_fields
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hrecordRows : record.input.rows = z.1.1.2 := by
    simpa [record, originalSourceCurrentRecord, originalSourceCurrentInput,
      ReferenceActivePhysicalHorizon.roundInputAt] using hfields.1
  have hrecordSelected : record.input.selected = q := by
    simpa [record, originalSourceCurrentRecord, originalSourceCurrentInput,
      ReferenceActivePhysicalHorizon.roundInputAt] using hfields.2.1
  obtain ⟨test', htest', htime, hsample, hsent⟩ :=
    ReferenceGeneratedUpBatchPrefixEvent.actualRecordUpTest_sourceFields
      (p := p) (rate := rate) i record diagnostic z.1.1.2 q
      hrecordRows hrecordSelected hdiagnostic hselectedDiagnostic heligible
  have htests : test = test' := upTest_eq_of_both i diagnostic test test' htestCurrent htest'
  subst test'
  have hexpected := ReferenceGeneratedUpBatchPrefixEvent.actualRecordUpDiagnostic_expected
    record diagnostic hdiagnostic
  refine ⟨test, htest, ?_, hsample, ?_⟩
  · have htime' : test.time = record.input.time.val := by
      simpa [hdiagnostic, ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic,
        hselectedDiagnostic, heligible] using htime
    simpa [record, originalSourceCurrentRecord, originalSourceCurrentInput,
      ReferenceActivePhysicalHorizon.roundInputAt] using htime'
  · calc
      test.sent = diagnostic.expected := by
        simpa [hdiagnostic, ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic,
          hselectedDiagnostic, heligible] using hsent
      _ = ReferenceActiveAffinePositiveTest.upSent record.input := hexpected
      _ = ReferenceActiveAffinePositiveTest.upSent
          (originalSourceCurrentInput (rate := rate) rewards C_star C_h q t s hs control0 i z) := rfl

/-- Every selected-i diagnostic test in the actual original `[s,t)` prefix
has its original row sample and the executed UP offer. All diagnostic and
eligibility inputs are recovered by inverting the actual test projection. -/
theorem originalSourcePrefixRecord_upTest_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : UpLaunchSource (rate := rate) rewards C_star C_h q t s i)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ (ReferenceActiveHorizonMeasurability.runOfInput s
      (t.val - s) (by omega)
      (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
        (rate := rate) rewards C_star C_h q t s hs control0 i z)).records)
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (test : AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p))
    (htest : ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
      (p := p) (rate := rate) i (some diagnostic) = some test) :
    test.time = record.input.time.val ∧
      test.sample = ((z.1.1.2 q).2 record.input.time).2 (1, i) ∧
      test.sent = ReferenceActiveAffinePositiveTest.upSent record.input := by
  have hselected : diagnostic.input.selectedFollower = i := by
    exact (upTest_condition i diagnostic test htest).1
  have heligible : AffineBatchDecoder.eligible
      (CoordinatorUpReception.roundInput diagnostic.input) := by
    exact (upTest_condition i diagnostic test htest).2
  obtain ⟨_, _, _, _, _, _, test', htest', htime, hsample, hsent⟩ :=
    ReferenceGeneratedUpBatchPrefixEvent.originalSourceRun_recordUpTest_fields
      (rate := rate) rewards C_star C_h q t s hs control0 i z record hrecord
      diagnostic hdiagnostic hselected heligible
  have htests : test' = test := by
    have h := htest
    have h' := htest'
    simp [ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic,
      hselected, heligible] at h h'
    exact (upTest_eq_of_both i diagnostic test test' htest htest').symm
  subst test'
  exact ⟨htime, hsample, hsent⟩

/-- Literal actual UP source event: the original source-generated launch,
the arbitrary-alpha actual prefix marker, and the current executed positive
UP test whose saved offer differs from the deterministic candidate. -/
def actualUpPrefixPositiveSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) : Set (SourceInput p) :=
  {z | ∃ hz : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h q t (1, i) s,
    ReferenceGeneratedUpBatchPrefixEvent.originalSourcePrefixMarker
        (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i
        ⟨z, hz⟩ ∧
      ∃ test, ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
        (p := p) (rate := rate) i
        (originalSourceCurrentRecord (rate := rate)
          rewards C_star C_h q t s hs control0 i ⟨z, hz⟩).output.coordinator.up =
          some test ∧ test.sent ≠ some candidate}

/-- Refine the actual event by the hash-one value of the original source
pair at the selected coordinator row and physical time. -/
def actualUpPrefixPositiveHashOneSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) : Set (SourceInput p) :=
  {z | z ∈ actualUpPrefixPositiveSourceEvent (rate := rate)
      rewards C_star C_h q t s hs control0 alpha ell candidate i ∧
    AffineChannelLaw.affineHash (((z.1.2 q).2 t).2 (1, i)) candidate = 1}

private theorem originalSourcePrefixMarker_iff_cylinder
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) (a : ReferenceGeneratedAffineHashHalf.Pair p)
    (r : PairRemainder p q t i)
    (hbranch : (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (1, i)).symm (a, r) ∈
      ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h q t (1, i) s) :
    ReferenceGeneratedUpBatchPrefixEvent.originalSourcePrefixMarker
        (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i
        ⟨(ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (1, i)).symm (a, r), hbranch⟩ ↔
      r ∈ ReferenceGeneratedUpBatchPrefixEvent.upBatchPrefixCylinder
        (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i := by
  have hbranchR := (ReferenceGeneratedAffineHashHalf.generatedLaunchBranch_fixedPairSplit_iff
    (rate := rate) rewards C_star C_h q t (1, i) s hs control0 a r).mp hbranch
  change r ∈ ReferenceSelectedAffinePairLaw.remainderSelectorEvent p q t (1, i) ∧ _ at hbranchR
  have hsplit := ReferenceGeneratedUpBatchPrefixEvent.upBatchPrefixSourceEvent_fixedPairSplit_iff
    (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i a r
  constructor
  · intro hmarker
    have hsource : (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (1, i)).symm (a, r) ∈
        ReferenceGeneratedUpBatchPrefixEvent.upBatchPrefixSourceEvent
          (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i :=
      ⟨hbranch, hmarker⟩
    exact (hsplit.mp hsource).2
  · intro hcylinder
    have hsource := hsplit.mpr ⟨hbranchR.1, hcylinder⟩
    obtain ⟨_, hmarker⟩ := hsource
    exact hmarker

/-- The actual current-test event is exactly A's source event with U's
concrete arbitrary-birth prefix cylinder. -/
theorem actualUpPrefixPositiveSourceEvent_eq_generatedPositiveSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) :
    actualUpPrefixPositiveSourceEvent (rate := rate)
        rewards C_star C_h q t s hs control0 alpha ell candidate i =
      ReferenceGeneratedAffineHashHalf.generatedPositiveSourceEvent
        (rate := rate) rewards C_star C_h q t 1 i s hs control0 candidate
        (ReferenceGeneratedUpBatchPrefixEvent.upBatchPrefixCylinder
          (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i) := by
  classical
  ext z
  let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (1, i)
  rcases hsplit : split z with ⟨a, r⟩
  have hrecover : split.symm (a, r) = z := by
    rw [← hsplit]
    exact split.symm_apply_apply z
  rw [← hrecover]
  change (∃ hz : split.symm (a, r) ∈
      ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h q t (1, i) s,
      ReferenceGeneratedUpBatchPrefixEvent.originalSourcePrefixMarker
          (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i
          ⟨split.symm (a, r), hz⟩ ∧
        ∃ test, ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
            (p := p) (rate := rate) i
            (originalSourceCurrentRecord (rate := rate)
              rewards C_star C_h q t s hs control0 i ⟨split.symm (a, r), hz⟩).output.coordinator.up =
              some test ∧ test.sent ≠ some candidate) ↔ _
  constructor
  · rintro ⟨hz, hmarker, test, htest, hsent⟩
    have hC := originalSourcePrefixMarker_iff_cylinder
      (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i a r hz |>.mp hmarker
    have hpositive := (originalSourceCurrentRecord_upTest_iff (rate := rate)
      rewards C_star C_h q t s hs control0 i ⟨split.symm (a, r), hz⟩).mpr ⟨test, htest⟩
    obtain ⟨test', htest', _, _, hsentFields⟩ :=
      originalSourceCurrentRecord_upPositive_fields (rate := rate)
        rewards C_star C_h q t s hs control0 i ⟨split.symm (a, r), hz⟩ hpositive
    have htests : test = test' := by
      have htestRecord : ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
          (p := p) (rate := rate) i
          (originalSourceCurrentRecord (rate := rate)
            rewards C_star C_h q t s hs control0 i ⟨split.symm (a, r), hz⟩).output.coordinator.up =
            some test := by
        simpa [originalSourceCurrentRecord] using htest
      obtain ⟨d, hd, hleft⟩ := diagnostic_of_upTest i
        (originalSourceCurrentRecord (rate := rate)
          rewards C_star C_h q t s hs control0 i ⟨split.symm (a, r), hz⟩).output.coordinator.up
        test htestRecord
      have hright : ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
          (p := p) (rate := rate) i (some d) = some test' := by
        simpa [hd] using htest'
      exact upTest_eq_of_both i d test test' hleft hright
    subst test'
    have hsentActual : ReferenceActiveAffinePositiveTest.upSent
        (originalSourceCurrentInput (rate := rate) rewards C_star C_h q t s hs control0 i
          ⟨split.symm (a, r), hz⟩) ≠ some candidate := by
      intro h
      exact hsent (hsentFields.trans h)
    have hpositive' : ReferenceGeneratedAffineHashHalf.directionPositive 1
        (ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch
          (rate := rate) rewards C_star C_h q t (1, i) s hs control0
          ⟨split.symm (a, r), hz⟩) = true := by
      simpa [ReferenceGeneratedAffineHashHalf.directionPositive,
        originalSourceCurrentInput_eq_generatedNextInput]
        using hpositive
    have hsent' : ReferenceGeneratedAffineHashHalf.directionSent 1
        (ReferenceGeneratedAffineHashHalf.generatedNextInputOfBranch
          (rate := rate) rewards C_star C_h q t (1, i) s hs control0
          ⟨split.symm (a, r), hz⟩) ≠ some candidate := by
      simpa [ReferenceGeneratedAffineHashHalf.directionSent,
        originalSourceCurrentInput_eq_generatedNextInput]
        using hsentActual
    exact ⟨hz, by simpa [split] using hC, hpositive', hsent'⟩
  · rintro ⟨hz, hC, hpositive, hsent⟩
    change (split (split.symm (a, r))).2 ∈
      ReferenceGeneratedUpBatchPrefixEvent.upBatchPrefixCylinder
        (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i at hC
    rw [split.apply_symm_apply] at hC
    have hmarker := originalSourcePrefixMarker_iff_cylinder
      (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i a r hz |>.mpr hC
    have hactualPositive : ReferenceActiveAffinePositiveTest.upPositive
        (originalSourceCurrentInput (rate := rate) rewards C_star C_h q t s hs control0 i
          ⟨split.symm (a, r), hz⟩) = true := by
      simpa [ReferenceGeneratedAffineHashHalf.directionPositive,
        originalSourceCurrentInput_eq_generatedNextInput]
        using hpositive
    obtain ⟨test, htest⟩ := (originalSourceCurrentRecord_upTest_iff (rate := rate)
      rewards C_star C_h q t s hs control0 i ⟨split.symm (a, r), hz⟩).mp hactualPositive
    obtain ⟨test', htest', _, _, hsentFields⟩ :=
      originalSourceCurrentRecord_upPositive_fields (rate := rate)
        rewards C_star C_h q t s hs control0 i ⟨split.symm (a, r), hz⟩ hactualPositive
    have htests : test = test' := by
      have htestRecord : ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
          (p := p) (rate := rate) i
          (originalSourceCurrentRecord (rate := rate)
            rewards C_star C_h q t s hs control0 i ⟨split.symm (a, r), hz⟩).output.coordinator.up =
            some test := by
        simpa [originalSourceCurrentRecord] using htest
      obtain ⟨d, hd, hleft⟩ := diagnostic_of_upTest i
        (originalSourceCurrentRecord (rate := rate)
          rewards C_star C_h q t s hs control0 i ⟨split.symm (a, r), hz⟩).output.coordinator.up
        test htestRecord
      have hright : ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
          (p := p) (rate := rate) i (some d) = some test' := by
        simpa [hd] using htest'
      exact upTest_eq_of_both i d test test' hleft hright
    subst test'
    have hsentActual : ReferenceActiveAffinePositiveTest.upSent
        (originalSourceCurrentInput (rate := rate) rewards C_star C_h q t s hs control0 i
          ⟨split.symm (a, r), hz⟩) ≠ some candidate := by
      simpa [ReferenceGeneratedAffineHashHalf.directionSent,
        originalSourceCurrentInput_eq_generatedNextInput]
        using hsent
    have hsentTest : test.sent ≠ some candidate := by
      intro h
      exact hsentActual (hsentFields.symm.trans h)
    exact ⟨hz, hmarker, test, htest, hsentTest⟩

/-- The hash-one refinement is the corresponding literal original-source
hash refinement of A's generated UP event. -/
theorem actualUpPrefixPositiveHashOneSourceEvent_eq_generatedPositiveHashOneSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) :
    actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
        rewards C_star C_h q t s hs control0 alpha ell candidate i =
      ReferenceGeneratedAffineHashHalf.generatedPositiveHashOneSourceEvent
        (rate := rate) rewards C_star C_h q t 1 i s hs control0 candidate
        (ReferenceGeneratedUpBatchPrefixEvent.upBatchPrefixCylinder
          (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i) := by
  change {z | z ∈ actualUpPrefixPositiveSourceEvent (rate := rate)
      rewards C_star C_h q t s hs control0 alpha ell candidate i ∧
      AffineChannelLaw.affineHash (((z.1.2 q).2 t).2 (1, i)) candidate = 1} = _
  rw [actualUpPrefixPositiveSourceEvent_eq_generatedPositiveSourceEvent]
  rfl

/-- The actual arbitrary-birth positive UP source event is Borel. Its
cylinder premise is supplied by U's proved Borel result. -/
theorem measurableSet_actualUpPrefixPositiveSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) :
    MeasurableSet (actualUpPrefixPositiveSourceEvent (rate := rate)
      rewards C_star C_h q t s hs control0 alpha ell candidate i) := by
  rw [actualUpPrefixPositiveSourceEvent_eq_generatedPositiveSourceEvent]
  exact ReferenceGeneratedAffineHashHalf.measurableSet_generatedPositiveSourceEvent
    (rate := rate) rewards C_star C_h q t 1 i s hs control0 candidate
    (ReferenceGeneratedUpBatchPrefixEvent.upBatchPrefixCylinder
      (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i)
    (ReferenceGeneratedUpBatchPrefixEvent.measurableSet_upBatchPrefixCylinder
      (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i)

/-- The actual positive-UP event with source-pair hash one is Borel on the
original continuous/private source space. -/
theorem measurableSet_actualUpPrefixPositiveHashOneSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) :
    MeasurableSet (actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
      rewards C_star C_h q t s hs control0 alpha ell candidate i) := by
  rw [actualUpPrefixPositiveHashOneSourceEvent_eq_generatedPositiveHashOneSourceEvent]
  exact ReferenceGeneratedAffineHashHalf.measurableSet_generatedPositiveHashOneSourceEvent
    (rate := rate) rewards C_star C_h q t 1 i s hs control0 candidate
    (ReferenceGeneratedUpBatchPrefixEvent.upBatchPrefixCylinder
      (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i)
    (ReferenceGeneratedUpBatchPrefixEvent.measurableSet_upBatchPrefixCylinder
      (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i)

/-- Membership in the literal event gives the actual positive diagnostic
test, including its time, original sample and saved `upSent` option. -/
theorem actualUpPrefixPositiveSourceEvent_test_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) (z : SourceInput p)
    (hevent : z ∈ actualUpPrefixPositiveSourceEvent (rate := rate)
      rewards C_star C_h q t s hs control0 alpha ell candidate i) :
    ∃ hz : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h q t (1, i) s,
      ReferenceGeneratedUpBatchPrefixEvent.originalSourcePrefixMarker
        (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i ⟨z, hz⟩ ∧
      ∃ test, ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
          (p := p) (rate := rate) i
          (originalSourceCurrentRecord (rate := rate)
            rewards C_star C_h q t s hs control0 i ⟨z, hz⟩).output.coordinator.up = some test ∧
        test.time = t.val ∧ test.sample = ((z.1.2 q).2 t).2 (1, i) ∧
        test.sent = ReferenceActiveAffinePositiveTest.upSent
          (originalSourceCurrentInput (rate := rate) rewards C_star C_h q t s hs control0 i
            ⟨z, hz⟩) := by
  obtain ⟨hz, hmarker, test, htest, _⟩ := hevent
  have hpositive := (originalSourceCurrentRecord_upTest_iff (rate := rate)
    rewards C_star C_h q t s hs control0 i ⟨z, hz⟩).mpr ⟨test, htest⟩
  obtain ⟨test', htest', htime, hsample, hsent⟩ :=
    originalSourceCurrentRecord_upPositive_fields (rate := rate)
      rewards C_star C_h q t s hs control0 i ⟨z, hz⟩ hpositive
  have htests : test = test' := by
    have htestRecord : ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
        (p := p) (rate := rate) i
        (originalSourceCurrentRecord (rate := rate)
          rewards C_star C_h q t s hs control0 i ⟨z, hz⟩).output.coordinator.up = some test := by
      simpa [originalSourceCurrentRecord] using htest
    obtain ⟨d, hd, hleft⟩ := diagnostic_of_upTest i
      (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i ⟨z, hz⟩).output.coordinator.up
      test htestRecord
    have hright : ReferenceGeneratedUpBatchPrefixEvent.upTestOfDiagnostic
        (p := p) (rate := rate) i (some d) = some test' := by
      simpa [hd] using htest'
    exact upTest_eq_of_both i d test test' hleft hright
  subst test'
  exact ⟨hz, hmarker, test, htest, htime, hsample, hsent⟩

/-- The original product-source law assigns exactly half of the actual UP
prefix-positive event to its original-pair hash-one refinement. -/
theorem actualUpPrefixPositive_hash_half
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
          rewards C_star C_h q t s hs control0 alpha ell candidate i) =
      ((1 : ℝ≥0∞) / 2) *
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (actualUpPrefixPositiveSourceEvent (rate := rate)
            rewards C_star C_h q t s hs control0 alpha ell candidate i) := by
  rw [actualUpPrefixPositiveHashOneSourceEvent_eq_generatedPositiveHashOneSourceEvent,
    actualUpPrefixPositiveSourceEvent_eq_generatedPositiveSourceEvent]
  exact ReferenceGeneratedAffineHashHalf.upGeneratedPositive_hash_half
    (rate := rate) rewards C_star C_h q t i s hs control0 candidate
    (ReferenceGeneratedUpBatchPrefixEvent.upBatchPrefixCylinder
      (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i)
    (ReferenceGeneratedUpBatchPrefixEvent.measurableSet_upBatchPrefixCylinder
      (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i)

end Bandits.Support.ReferenceGeneratedUpPrefixPositiveHalf

end
