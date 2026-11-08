/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownLaterCompletionDetector
public import Bandits.Support.ReferenceGeneratedLiveStaleDownExclusion

import Lean.Elab.Tactic.Omega

/-!
# Continuing-LIVE later DOWN completion containment

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,111-157`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42,60-124`,
`sources/zip4/manuscript/06_interruptions.tex:246-295,327-348`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The export covers one actual wrong uniquely accepted DOWN cut on a selected
continuing-LIVE branch, when this completion is later than an actual earlier
completion in the same generated run. It discharges the detector's per-test
not-sent premise from actual earlier selected tests and the current actual cut.
It does not close the first-completion, collection, failure, or global regret
events.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceGeneratedDownBatchCalendar
open ReferenceGeneratedInheritedDownWrongCompletionWitness

namespace Bandits.Support.ReferenceGeneratedLiveLaterCompletionContainment

variable {p : ConstructorDimensions.Parameters}

private theorem reference_cut_expected_ne_raw
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hfalse : (ReferenceDownReception.referenceDownCut p view i row time observation
      rate state).rawComparison = some false)
    (hraw : (ReferenceDownReception.referenceDownCut p view i row time observation
      rate state).raw = some word) :
    (ReferenceDownReception.referenceDownCut p view i row time observation
      rate state).expectedWord ≠ some word := by
  classical
  have hcompared : (ReferenceDownReception.referenceDownCut p view i row time observation
      rate state).rawComparison ≠ none := by
    rw [hfalse]
    decide
  have hrawStep := ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
    view i row time observation rate state hcompared
  have hdecoded := hrawStep.symm.trans hraw
  intro hexpected
  have hcall := ReferenceActiveAffinePositiveTest.referenceDownCut_has_call
    view i row time observation state
  rw [hfalse] at hcall
  have hgate : ReferenceActiveAffinePositiveTest.downReceiverGate i row time state :=
    of_decide_eq_true (by simpa using hcall)
  rcases hgate with ⟨hselected, hstatus, hregisters, hbatch, hbuffer⟩
  by_cases hmatches : (ActiveFollowerDownAcceptance.currentDecodeStep
      p i row time observation rate state).2 =
        ReferenceDownReception.expectedDownFlatWord view i row time
  · have htrue : (ReferenceDownReception.referenceDownCut p view i row time observation
        rate state).rawComparison = some true := by
      simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
        hregisters, hbatch, hbuffer, hmatches]
    rw [hfalse] at htrue
    cases htrue
  · have hexpected' : ReferenceDownReception.expectedDownFlatWord view i row time =
        some word := by
      simpa [ReferenceDownReception.referenceDownCut, hselected, hstatus,
        hregisters, hbatch, hbuffer, hmatches] using hexpected
    exact hmatches (hdecoded.trans hexpected'.symm)

private theorem actual_record_cut_expected_ne_raw
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hlogged : (record.output.followers i).downInput = some logged)
    (hcut : (record.output.followers i).down = some cut)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hfalse : cut.rawComparison = some false)
    (hraw : cut.raw = some word) :
    cut.expectedWord ≠ some word := by
  have hcutActual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    record i logged cut hlogged hcut
  have hfalse' := hfalse
  rw [hcutActual] at hfalse'
  have hraw' := hraw
  rw [hcutActual] at hraw'
  have hnot := reference_cut_expected_ne_raw rate
    record.output.preparation.coordinator.downView i record.input.row record.input.time
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) logged word
    hfalse' hraw'
  rw [hcutActual]
  exact hnot

/-- An actual later completion with a wrong uniquely accepted DOWN cut on the
selected continuing-LIVE branch belongs to the literal generated DOWN cohort
union. The earlier completion eliminates the detector's first-completion
alternative. Every test's not-sent condition is proved from its actual source
record and cut; no batch-wide or earlier-selection law is assumed.
-/
theorem generated_live_later_wrong_down_batch_mem_cohort
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (control0 : ContinuousLearningRows.TimeControl p)
    (hcomplete : ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
        rate rewards C_star C_h s hs i x).2 n))
    (hprevious : ∃ m : Fin (p.T - s), m.val < n.val ∧
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
        ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
          rate rewards C_star C_h s hs i x).2 m))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x n).output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut) :
    match (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x n).output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen _ _ _ _) =>
        x.val ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
          rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)
    | _ => True := by
  classical
  let Rk := fun k : Fin (p.T - s) =>
    ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x k
  let O := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
    rate rewards C_star C_h s hs i x
  let Comp := fun k : Fin (p.T - s) =>
    ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (O.2 k)
  let detectorRecord := fun k : Fin (p.T - s) =>
    (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega)
        (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
          rate rewards C_star C_h s hs x),
      ReferenceActivePhysicalStep.step
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega)
          (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
            rate rewards C_star C_h s hs x)), rfl⟩ :
      ReferenceFollowerDownDecoderReplay.Record p rate)
  have hsameRecord : ∀ k : Fin (p.T - s), detectorRecord k = Rk k := by
    intro k
    rfl
  have hcomplete' : Comp n := by
    simpa only [Comp, O] using hcomplete
  have hprevious' : ∃ m : Fin (p.T - s), m.val < n.val ∧ Comp m := by
    simpa only [Comp, O] using hprevious
  have hcutDetector : ((detectorRecord n).output.followers i).down = some cut := by
    rw [hsameRecord n]
    exact hcut
  cases hcoordinator : (Rk n).output.preparation.coordinator with
  | first _ => trivial
  | live registers owned base outcome =>
      cases outcome with
      | clockFailure _ _ => trivial
      | initializerFailure _ _ _ _ => trivial
      | localFailure _ _ _ => trivial
      | cutoffChosen _ _ _ _ _ _ _ _ _ _ => trivial
      | continuingChosen dispatched _ _ _ =>
          cases hselection : (Rk n).output.preparation.coordinator.selection with
          | none =>
              rw [hcoordinator] at hselection
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt] at hselection
          | some v =>
              have hv : (Rk n).output.preparation.coordinator.selection = some v :=
                hselection
              cases hraw : cut.raw with
              | none => exact False.elim (hwrong.2.1 hraw)
              | some word =>
                  have hcutG : ((detectorRecord n).output.followers i).down = some cut :=
                    hcutDetector
                  have hdetector :=
                    ReferenceGeneratedDownLaterCompletionDetector.generated_down_later_raw_detector_of_not_sent
                      rate rewards C_star C_h s hs x i n cut word control0 hcomplete' hcutG hraw
                  dsimp only at hdetector
                  rcases hdetector with hfirst |
                    ⟨m, hmn, hcompm, hgreatest, hnoMiddle, hunique,
                      halpha, halphaN, hspanT, halphaT, hboundary,
                      callCodeN, loggedN, cutN, testN, hcallN, hactualN, hloggedN,
                      hcutN, hcomparisonN, hpositiveN, hquotaN, htestN,
                      hlistA, hlistB, hlength, hcountBeforeN, hbank, hrawN,
                      hchron, hprovenance, hhash, hgoodDetector⟩
                  · rcases hprevious' with ⟨m', hm'n, hcompm'⟩
                    exact False.elim ((hfirst m' (Fin.lt_def.mpr hm'n)) hcompm')
                  · let a := m.val + 1
                    let alpha := s + a
                    let tests := ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
                      rate rewards C_star C_h s hs i alpha x
                    have hnotSent : ∀ test ∈ tests, test.sent ≠ some word := by
                      intro test hmem
                      rcases hprovenance test hmem with
                        ⟨k, _hak, hkN, _htest, _htime, _hsample, _hsent,
                          callCode, logged, cut', _hcall, _hactual, hlogged,
                          hcut', _hcomparison, _hpositive, hsentExpected⟩
                      by_cases hk : k.val < n.val
                      · intro hsentWord
                        have hexpected : cut'.expectedWord = some word :=
                          hsentExpected.symm.trans hsentWord
                        have hcutSource : ((Rk k).output.followers i).down = some cut' := by
                          rw [← hsameRecord k]
                          exact hcut'
                        obtain ⟨old, hold, _hbranch, _hword, _hparse, _hencode⟩ :=
                          ReferenceGeneratedInheritedDownCandidateOrigin.actual_expectedDownWord_origin
                            (Rk k) i cut' word hcutSource hexpected
                        have hnoEarlier :=
                          ReferenceGeneratedLiveStaleDownExclusion.generated_live_earlier_selected_test_raw_excluded
                            rate rewards C_star C_h s hs x n i
                        dsimp only at hnoEarlier
                        rw [hcoordinator] at hnoEarlier
                        have hv' := hv
                        rw [hcoordinator] at hv'
                        have hsentCut : cut'.expectedWord = cut.raw :=
                          (hsentExpected.symm.trans hsentWord).trans hraw.symm
                        exact hnoEarlier v hv' cut hcut hwrong k hk old hold cut'
                          hcutSource hsentCut
                      · have hkn : k.val = n.val := by omega
                        have hkEq : k = n := Fin.ext hkn
                        subst k
                        intro hsentWord
                        have hcutSource : ((Rk n).output.followers i).down = some cut' := by
                          rw [← hsameRecord n]
                          exact hcut'
                        have hcutEq : cut' = cut := by
                          apply Option.some.inj
                          calc
                            some cut' = ((Rk n).output.followers i).down := hcutSource.symm
                            _ = some cut := hcut
                        have hloggedSource :
                            ((Rk n).output.followers i).downInput = some logged := by
                          rw [← hsameRecord n]
                          exact hlogged
                        have hnotCurrent := actual_record_cut_expected_ne_raw
                          rate (Rk n) i logged cut hloggedSource hcut word hwrong.1 hraw
                        have hexpected : cut'.expectedWord = some word :=
                          hsentExpected.symm.trans hsentWord
                        rw [hcutEq] at hexpected
                        exact hnotCurrent hexpected
                    exact (hgoodDetector hnotSent).2
  | collection _ _ _ _ _ => trivial
  | invalidCollectionCutoff => trivial
  | dagger => trivial

end Bandits.Support.ReferenceGeneratedLiveLaterCompletionContainment

end
