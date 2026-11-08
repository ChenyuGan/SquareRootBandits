/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInheritedDownCandidateOrigin
public import Bandits.Support.ReferenceFirstDownRecoveryBudget
public import Bandits.Support.ReferenceFirstLiveRawDownExclusion

/-!
# First-live cut for an inherited DOWN completion

The earlier-sent obstruction from the generated inherited-DOWN witness is
eliminated when its actual sender and the current selected payload lie in the
same first-live window. The mixed detector and the two physical residuals are
kept explicit.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-106`,
`sources/zip4/manuscript/05_binary_transport.tex:74-78,100-103`,
`sources/zip4/manuscript/06_interruptions.tex:270-275,286-289,327-344`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-33`.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceDownReception
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceGeneratedInheritedDownWrongCompletionWitness
open Bandits.Support.ReferenceGeneratedInheritedDownCandidateOrigin
open Bandits.Support.ReferenceSelectedPayloadChronology
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceFirstLivePendingErasureHistory

namespace Bandits.Support.ReferenceGeneratedInheritedDownFirstLiveCut

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

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

/-- The selected inherited first-live component of the generated wrong-DOWN
completion cut. The conclusion retains the source batch boundary and all
original hash and birth witnesses, with explicit first-live and no-selection
residuals for later consumers.
-/
theorem generated_inherited_firstLive_wrong_completion_cut
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
        F.length ≤ n.val ∨
        Rn.output.preparation.coordinator.selection = none) := by
  classical
  let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
    rate rewards C_star C_h s hs x i).downBatch
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  let E := ReferenceGeneratedDownBatchCalendar.generatedSourceRun
    rate rewards C_star C_h s hs x
  let F := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  let Rn := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
    rate rewards C_star C_h s hs x n

  have hbase :=
    ReferenceGeneratedInheritedDownCandidateOrigin.generated_inherited_down_candidate_origin
      rate rewards C_star C_h s hs x i n control0 hfirst hwrong
  rcases hbase with ⟨cut, word, alpha, hAlpha, hcut, hwrongCut, hraw, hAlphaS,
    hbirth, hboundary, hhash, hcurrentSuffix, hobstruction⟩
  refine ⟨cut, word, alpha, hAlpha, hcut, hwrongCut, hraw, hAlphaS,
    hbirth, hboundary, hhash, hcurrentSuffix, ?_⟩
  rcases hobstruction with hdetector | hearlier
  · exact Or.inl hdetector
  · rcases hearlier with ⟨earlier, hearlierPrefix, hearlierSent, offset,
      record, hrecordRun, hrecordSuffix, hrecordTime, htimeOrder, hearlierTime,
      hexecuted, call, cutEarlier, hcall, hcutEarlier, hearlierSample,
      hexpectedEarlier, selected, hselectedEarlier, hsenderEarlier,
      message, hmessage, hwordMessage, hencode, hparseMessage, hcurrentParse,
      hsigmaMessage, birthRecord, hbirthRecord, hinstallation, hbirthTime,
      hbirthBefore⟩
    by_cases hwindow : n.val < F.length
    · cases hcurrent : Rn.output.preparation.coordinator.selection with
      | none => exact Or.inr (Or.inr rfl)
      | some current =>
          have hcurrentSelection :
              Rn.output.preparation.coordinator.selection = some current := hcurrent

          have hseedSpec := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
            rate rewards C_star C_h s hs x
          have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s :=
            hseedSpec.2.1
          obtain ⟨active, hactive, _hactiveUnique⟩ :=
            ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
              rate x.val rewards C_star C_h x.property.1
          have hseedActive : seed = active :=
            Option.some.inj (hseedSpec.1.symm.trans hactive.1)
          have hinitial : seed.coordinator = .first := by
            rw [hseedActive]
            exact hactive.2.1
          obtain ⟨activeFields, hfieldsLaunch, hfields⟩ :=
            ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
              rate x.val rewards C_star C_h x.property.1
          have hseedFields : seed = activeFields :=
            Option.some.inj (hseedSpec.1.symm.trans hfieldsLaunch)
          have hinitialFollowers :
              ReferenceFirstLiveConfirmationHistory.InitialFollowers seed := by
            intro j state memory hstate
            rcases hfields j with ⟨hconfiguration, hlastDown, _, _, _, _,
              hunoccupied, _, _⟩
            have hconfiguration' :
                seed.followers j = .ordinary
                  (ReferenceInitializationRun.ordinary
                    (ActualReferenceInitializationBlock.referenceInput x.val rewards
                      C_star C_h rate)
                    (ReferenceInitializationRun.output
                      (ActualReferenceInitializationBlock.referenceInput x.val rewards
                        C_star C_h rate))
                    (ActualReferenceInitializationBlock.refFollower j))
                  (ActiveFollowerLifecycle.initialMemory p) := by
              rw [hseedFields]
              exact hconfiguration
            rw [hconfiguration'] at hstate
            cases hstate
            exact ⟨hunoccupied, hlastDown⟩

          let actualRun := ReferenceActivePhysicalHorizon.run seed (x.val.1.2)
            (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s
            (p.T - s) (by omega) hmode
          have hrunEq : E = actualRun := by
            dsimp [E, actualRun, ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
              ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput,
              ReferenceActiveHorizonMeasurability.runOfInput, seed]
          have hFactual : F =
              ReferenceFirstLiveConfirmationHistory.firstLiveWindow actualRun.records := by
            dsimp only [F]
            rw [hrunEq]
          let Factual := ReferenceFirstLiveConfirmationHistory.firstLiveWindow actualRun.records
          have hwindowActual : n.val < Factual.length := by
            simpa only [Factual, hFactual] using hwindow
          have hFprefix : Factual.IsPrefix actualRun.records := List.takeWhile_prefix _

          have hsourceRecordGet? : E.records[n.val]? = some Rn :=
            ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
              rate rewards C_star C_h s hs x n
          have hactualRecordGet? : actualRun.records[n.val]? = some Rn := by
            simpa only [hrunEq] using hsourceRecordGet?
          have hrunCountActual : actualRun.records.length = p.T - s :=
            ReferenceActivePhysicalHorizon.run_record_count seed (x.val.1.2)
              (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s
              (p.T - s) (by omega) hmode
          have hnActual : n.val < actualRun.records.length := by
            rw [hrunCountActual]
            exact n.isLt
          have hRnActual : actualRun.records[n.val]'hnActual = Rn :=
            Option.some.inj
              ((List.getElem?_eq_getElem hnActual).symm.trans hactualRecordGet?)
          have hRnWindow : Factual[n.val]'hwindowActual = Rn := by
            calc
              Factual[n.val]'hwindowActual = actualRun.records[n.val]'(by
                exact lt_of_lt_of_le hwindowActual hFprefix.length_le) :=
                  hFprefix.getElem hwindowActual
              _ = Rn := hRnActual

          have htimes : actualRun.records.map (fun r => r.input.time.val) =
              ReferenceActivePhysicalHorizon.calendar s (p.T - s) := by
            exact ReferenceActivePhysicalHorizon.run_time_values seed (x.val.1.2)
              (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s
              (p.T - s) (by omega) hmode
          have hrecordTimeAt (j : ℕ) (hj : j < actualRun.records.length) :
              (actualRun.records[j]'hj).input.time.val = s + j := by
            have hjRange : j < p.T - s := by
              rw [← hrunCountActual]
              exact hj
            have hget := congrArg (fun values : List ℕ => values[j]?) htimes
            simpa only [List.getElem?_map, List.getElem?_eq_getElem hj,
              ReferenceActivePhysicalHorizon.calendar, List.getElem?_range', hjRange,
              Option.map_some, Nat.one_mul, Option.some.injEq] using hget

          have hrecordRunActual : record ∈ actualRun.records := by
            rw [← hrunEq]
            exact hrecordRun
          obtain ⟨j, hj, hrecordAt⟩ := List.mem_iff_getElem.mp hrecordRunActual
          have hjTime : s + j = s + offset.val := by
            calc
              s + j = (actualRun.records[j]'hj).input.time.val :=
                (hrecordTimeAt j hj).symm
              _ = record.input.time.val := congrArg
                (fun r : ReferenceActivePhysicalHorizon.RoundRecord
                  (p := p) (rate := rate) => r.input.time.val) hrecordAt
              _ = s + offset.val := hrecordTime
          have hjOffset : j = offset.val := by omega
          have hoffsetBefore : offset.val < n.val := by omega
          have hoffsetWindow : offset.val < Factual.length :=
            lt_trans hoffsetBefore hwindowActual
          have hoffsetActual : offset.val < actualRun.records.length :=
            Nat.lt_of_lt_of_le hoffsetWindow hFprefix.length_le
          have hrecordAtOffset : actualRun.records[offset.val]'hoffsetActual = record := by
            simpa only [hjOffset] using hrecordAt
          have hrecordWindow : Factual[offset.val]'hoffsetWindow = record := by
            calc
              Factual[offset.val]'hoffsetWindow =
                  actualRun.records[offset.val]'(by
                    exact lt_of_lt_of_le hoffsetWindow hFprefix.length_le) :=
                hFprefix.getElem hoffsetWindow
              _ = record := hrecordAtOffset

          let currentWindow : ReferenceActivePhysicalStep.Selection
              Factual[n.val].input := hRnWindow.symm ▸ current
          let currentPair : Σ r : ReferenceActivePhysicalHorizon.RoundRecord
              (p := p) (rate := rate),
              ReferenceActivePhysicalStep.Selection r.input := ⟨Rn, current⟩
          let currentWindowPair : Σ r : ReferenceActivePhysicalHorizon.RoundRecord
              (p := p) (rate := rate),
              ReferenceActivePhysicalStep.Selection r.input :=
            ⟨Factual[n.val], currentWindow⟩
          have hcurrentPair : currentWindowPair = currentPair := by
            apply Sigma.ext hRnWindow
            exact eqRec_heq
              (φ := fun r : ReferenceActivePhysicalHorizon.RoundRecord
                (p := p) (rate := rate) =>
                ReferenceActivePhysicalStep.Selection r.input)
              hRnWindow.symm current
          have hselectedCurrentWindow :
              Factual[n.val].output.preparation.coordinator.selection = some currentWindow := by
            change currentWindowPair.1.output.preparation.coordinator.selection =
              some currentWindowPair.2
            rw [hcurrentPair]
            exact hcurrentSelection
          have hcurrentWindowPayload :
              currentWindow.view.payload = current.view.payload := by
            exact congrArg (fun pair : Σ r : ReferenceActivePhysicalHorizon.RoundRecord
              (p := p) (rate := rate), ReferenceActivePhysicalStep.Selection r.input =>
                pair.2.view.payload) hcurrentPair
          have hcurrentWindowView : currentWindow.view = current.view := by
            exact congrArg (fun pair : Σ r : ReferenceActivePhysicalHorizon.RoundRecord
              (p := p) (rate := rate), ReferenceActivePhysicalStep.Selection r.input =>
                pair.2.view) hcurrentPair
          let selectedWindow : ReferenceActivePhysicalStep.Selection
              Factual[offset.val].input :=
            hrecordWindow.symm ▸ selected
          let selectedPair : Σ r : ReferenceActivePhysicalHorizon.RoundRecord
              (p := p) (rate := rate),
              ReferenceActivePhysicalStep.Selection r.input := ⟨record, selected⟩
          let selectedWindowPair : Σ r : ReferenceActivePhysicalHorizon.RoundRecord
              (p := p) (rate := rate),
              ReferenceActivePhysicalStep.Selection r.input :=
            ⟨Factual[offset.val], selectedWindow⟩
          have hselectedPair : selectedWindowPair = selectedPair := by
            apply Sigma.ext hrecordWindow
            exact eqRec_heq
              (φ := fun r : ReferenceActivePhysicalHorizon.RoundRecord
                (p := p) (rate := rate) =>
                ReferenceActivePhysicalStep.Selection r.input)
              hrecordWindow.symm selected
          have hselectedEarlierWindow :
              Factual[offset.val].output.preparation.coordinator.selection = some selectedWindow := by
            change selectedWindowPair.1.output.preparation.coordinator.selection =
              some selectedWindowPair.2
            rw [hselectedPair]
            exact hselectedEarlier
          have hselectedWindowPayload :
              selectedWindow.view.payload = selected.view.payload := by
            exact congrArg (fun pair : Σ r : ReferenceActivePhysicalHorizon.RoundRecord
              (p := p) (rate := rate), ReferenceActivePhysicalStep.Selection r.input =>
                pair.2.view.payload) hselectedPair

          have hselectedPayload :=
            ReferenceFirstDownRecoveryBudget.run_first_selected_payload seed
              (x.val.1.2) (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards
              s (p.T - s) (by omega) hmode hinitial
          dsimp only at hselectedPayload
          have hcurrentFirstBirth :=
            hselectedPayload ⟨n.val, hwindowActual⟩ currentWindow hselectedCurrentWindow
          have hearlierFirstBirth :=
            hselectedPayload ⟨offset.val, hoffsetWindow⟩ selectedWindow hselectedEarlierWindow
          rcases hcurrentFirstBirth with ⟨_, _, _, _, hsigmaCurrentWindow, _⟩
          rcases hearlierFirstBirth with ⟨_, _, _, _, hsigmaEarlierWindow, _⟩
          have hsigmaCurrent : current.view.payload.sigma.val = s := by
            rw [← hcurrentWindowPayload]
            exact hsigmaCurrentWindow
          have hsigmaEarlier : selected.view.payload.sigma.val = s := by
            rw [← hselectedWindowPayload]
            exact hsigmaEarlierWindow

          have hpayloadCurrentRun : Rn ∈ actualRun.records := by
            rw [← hRnActual]
            exact List.getElem_mem hnActual
          have hpayloadEq :=
            ReferenceSelectedPayloadChronology.run_two_actualSelectedPayloads_eq_of_equal_sigma
              seed (x.val.1.2) (ActualInitializationPhysicalStep.selectedRowIndex p x.val)
              rewards s (p.T - s) (by omega) hmode hinitial Rn record current selected
              hpayloadCurrentRun hrecordRunActual hcurrentSelection hselectedEarlier
              (hsigmaCurrent.trans hsigmaEarlier.symm)
          have hwordCurrent : word =
              CoordinatorLocalArmChoice.storedDownFlatWord current.view.payload i := by
            exact hwordMessage.trans
              (congrArg (fun payload =>
                CoordinatorLocalArmChoice.storedDownFlatWord payload i) hpayloadEq).symm
          have hrecordCurrent : selected.view.payload.downRecord i =
              current.view.payload.downRecord i :=
            congrArg (fun payload => payload.downRecord i) hpayloadEq.symm
          have hparseCurrentPayload : cut.ordinaryParse =
              some (current.view.payload.downRecord i) := by
            calc
              cut.ordinaryParse = some message := hcurrentParse
              _ = some (selected.view.payload.downRecord i) := congrArg some hmessage
              _ = some (current.view.payload.downRecord i) := congrArg some hrecordCurrent

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
          by_cases hpending : i ∈ current.view.pendingAtChoice
          · have hsenderCurrent :
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
          · have hcurrentSelectedPrep :
                (ReferenceActivePhysicalStep.prepare Rn.input).coordinator.selection =
                  some current := by
              have h := hcurrentSelection
              rw [Rn.output_eq] at h
              simpa only [ReferenceActivePhysicalStep.step] using h
            have hcurrentSelectedWindowPrep :
                (ReferenceActivePhysicalStep.prepare (Factual[n.val].input)).coordinator.selection =
                  some currentWindow := by
              change (ReferenceActivePhysicalStep.prepare currentWindowPair.1.input).coordinator.selection =
                some currentWindowPair.2
              rw [hcurrentPair]
              exact hcurrentSelectedPrep
            have hparseCurrentWindow : cut.ordinaryParse =
                some (currentWindow.view.payload.downRecord i) := by
              rw [hcurrentWindowPayload]
              exact hparseCurrentPayload
            have hmissingWindow : i ∉ currentWindow.view.pendingAtChoice := by
              simpa only [hcurrentWindowView] using hpending
            have hnotAccepted :=
              ReferenceFirstLiveRawDownExclusion.run_firstLive_missing_pending_raw_down_diagnostic_excluded
                seed (x.val.1.2) (ActualInitializationPhysicalStep.selectedRowIndex p x.val)
                rewards s (p.T - s) (by omega) hmode hinitial hinitialFollowers
                ⟨n.val, hwindowActual⟩ currentWindow hcurrentSelectedWindowPrep i hmissingWindow
                ⟨n.val, hnActual⟩ (by simp)
                cut (by rw [hRnActual]; exact hcut) hparseCurrentWindow
            exact False.elim (hnotAccepted hwrongCut.2.2)
    · exact Or.inr (Or.inl (Nat.le_of_not_gt hwindow))

end Bandits.Support.ReferenceGeneratedInheritedDownFirstLiveCut

end
