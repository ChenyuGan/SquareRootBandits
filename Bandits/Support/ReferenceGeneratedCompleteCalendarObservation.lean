/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedSavedWrongEvent
public import Bandits.Support.ReferenceFirstLiveStoppedQueueComparison
import Lean.Elab.Tactic.Omega

/-!
# Complete actual reference calendar observation codes

Sources: `sources/zip4/manuscript/08_main_theorem.tex:26-75`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`,
`sources/zip4/manuscript/06_interruptions.tex:355-408`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/07_public_setup.tex:123-164`.

These definitions observe the existing complete physical suffix and its
existing optional coordinator trace. They preserve the original source, whole
reward table, continuous complete rows, private arrays, and selected row.
They do not interpret a missing call or diagnostic as a disabled round,
arrival, failure, or overflow, and establish no numerical arrival, source
error-event identity, probability law, concentration bound, or regret result.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceGeneratedDownAmbiguityMeasurability
open Bandits.Support.ReferenceCoordinatorRecorderCallTrace

namespace Bandits.Support.ReferenceGeneratedCompleteCalendarObservation

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev Rewards (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p

variable {p : Parameters} {rate : RateInput p}

/-- The actual chronological complete suffix, projected by H's existing
lossless whole-record encoder. -/
def completeSuffixCode (rewards : Rewards p) (C_star C_h : ℝ)
    (source : SourceInput p) : List (RoundRecordCode (p := p) (rate := rate)) :=
  (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).map
    (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate))

/-- The literal existing coordinator cell for each code, paired with the
same complete suffix code list. The option-valued selection, live, enabled,
and recorder diagnostics remain unchanged. -/
def completeRecorderTrace (rewards : Rewards p) (C_star C_h : ℝ)
    (source : SourceInput p) :=
  let codes := completeSuffixCode (rate := rate) rewards C_star C_h source
  (codes, codes.map (ReferenceCoordinatorRecorderCallTrace.cell (p := p) (rate := rate)))

private def launchStartCover (rewards : Rewards p) (C_star C_h : ℝ) : Set (SourceInput p) :=
  ⋃ s : Fin (p.T + 1),
    ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s.val

private theorem measurableSet_launchStartCover (rewards : Rewards p) (C_star C_h : ℝ) :
    MeasurableSet (launchStartCover (rate := rate) rewards C_star C_h) := by
  apply MeasurableSet.iUnion
  intro s
  exact ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
    (rate := rate) rewards C_star C_h s.val

private theorem mem_launchStartCover_iff (rewards : Rewards p) (C_star C_h : ℝ)
    (source : SourceInput p) :
    source ∈ launchStartCover (rate := rate) rewards C_star C_h ↔
      (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing.isSome = true := by
  constructor
  · intro h
    simp only [launchStartCover, Set.mem_iUnion] at h
    obtain ⟨s, hs⟩ := h
    change (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing.isSome = true ∧ _ at hs
    exact hs.1
  · intro h
    refine Set.mem_iUnion.mpr ⟨⟨ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h, ?_⟩, ?_⟩
    · have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
        rate source rewards C_star C_h
      omega
    · change (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing.isSome = true ∧
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = _
      exact ⟨h, rfl⟩

private theorem correctedLaunch_eq_none_of_not_mem_launchStartCover
    (rewards : Rewards p) (C_star C_h : ℝ) (source : SourceInput p)
    (hsource : source ∉ launchStartCover (rate := rate) rewards C_star C_h) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h = none := by
  have hcross : (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing.isSome ≠ true := by
    intro h
    exact hsource ((mem_launchStartCover_iff (rate := rate) rewards C_star C_h source).2 h)
  have hnone : (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing = none := by
    cases h : (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing with
    | none => rfl
    | some crossing => exact False.elim (hcross (by simp [h]))
  apply (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
    rate source rewards C_star C_h).2
  simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
    ReferenceCompletePhysicalHistory.generatedInput] using hnone

/-- Exact launch-fiber comparison with the existing H observation. `take`
is removed using the exact physical suffix length, including the zero-length
terminal-launch case. -/
private theorem completeSuffixCode_eq_runObservation (rewards : Rewards p)
    (C_star C_h : ℝ) (s : Fin (p.T + 1))
    (source : ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
      (rate := rate) rewards C_star C_h s.val) :
    completeSuffixCode (rate := rate) rewards C_star C_h source.1 =
      (ReferenceActiveHorizonMeasurability.runObservation (p := p) (rate := rate)
        s.val (p.T - s.val) (by omega)
        (ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
          (rate := rate) rewards C_star C_h s.val source)).2 := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate source.1 rewards C_star C_h = s.val := by
    have hfiber := source.property
    change _ ∧ ReferenceCompletePhysicalHistory.physicalStart rate source.1 rewards C_star C_h = s.val at hfiber
    exact hfiber.2
  have hlen : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source.1 rewards C_star C_h).length ≤ p.T - s.val := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length, hstart]
  unfold completeSuffixCode
  rw [ReferenceActiveHorizonMeasurability.runObservation_records,
    ReferenceGeneratedDownAmbiguityMeasurability.generatedRun_records_eq_completeSuffixRecords_take]
  rw [List.take_of_length_le hlen]

private def completeSuffixCover (rewards : Rewards p) (C_star C_h : ℝ)
    (tag : Option (Fin (p.T + 1))) : Set (SourceInput p) :=
  match tag with
  | none => (launchStartCover (rate := rate) rewards C_star C_h)ᶜ
  | some s => ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s.val

private def completeSuffixCoverCode (rewards : Rewards p) (C_star C_h : ℝ) :
    (tag : Option (Fin (p.T + 1))) →
      {source : SourceInput p // source ∈ completeSuffixCover (rate := rate) rewards C_star C_h tag} →
        List (RoundRecordCode (p := p) (rate := rate))
  | none, _ => []
  | some s, source =>
      (ReferenceActiveHorizonMeasurability.runObservation (p := p) (rate := rate)
        s.val (p.T - s.val) (by omega)
        (ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
          (rate := rate) rewards C_star C_h s.val ⟨source.1, source.2⟩)).2

private theorem measurableSet_completeSuffixCover (rewards : Rewards p) (C_star C_h : ℝ)
    (tag : Option (Fin (p.T + 1))) :
    MeasurableSet (completeSuffixCover (rate := rate) rewards C_star C_h tag) := by
  cases tag with
  | none =>
      exact (measurableSet_launchStartCover (rate := rate) rewards C_star C_h).compl
  | some s =>
      exact ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s.val

private theorem completeSuffixCover_iUnion_eq_univ (rewards : Rewards p) (C_star C_h : ℝ) :
    (⋃ tag, completeSuffixCover (rate := rate) rewards C_star C_h tag) = Set.univ := by
  ext source
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases hcross : source ∈ launchStartCover (rate := rate) rewards C_star C_h
  · simp only [launchStartCover, Set.mem_iUnion] at hcross
    obtain ⟨s, hs⟩ := hcross
    exact ⟨some s, hs⟩
  · exact ⟨none, hcross⟩

private theorem measurable_completeSuffixCoverCode (rewards : Rewards p) (C_star C_h : ℝ)
    (tag : Option (Fin (p.T + 1))) :
    Measurable (completeSuffixCoverCode (rate := rate) rewards C_star C_h tag) := by
  cases tag with
  | none => exact measurable_const
  | some s =>
      have hspan : s.val + (p.T - s.val) ≤ p.T := by omega
      change Measurable (fun source : ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
        (rate := rate) rewards C_star C_h s.val =>
          (ReferenceActiveHorizonMeasurability.runObservation (p := p) (rate := rate)
            s.val (p.T - s.val) hspan
            (ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
              (rate := rate) rewards C_star C_h s.val source)).2)
      exact (measurable_snd.comp
        (ReferenceActiveHorizonMeasurability.measurable_runObservation
          (p := p) (rate := rate) s.val (p.T - s.val) hspan)).comp
        (ReferenceGeneratedDownAmbiguityMeasurability.measurable_generatedActiveRunInput
          (rate := rate) rewards C_star C_h s.val)

private theorem completeSuffixCoverCode_compatible (rewards : Rewards p) (C_star C_h : ℝ) :
    ∀ (i j : Option (Fin (p.T + 1))) (source : SourceInput p)
      (hi : source ∈ completeSuffixCover (rate := rate) rewards C_star C_h i)
      (hj : source ∈ completeSuffixCover (rate := rate) rewards C_star C_h j),
      completeSuffixCoverCode (rate := rate) rewards C_star C_h i ⟨source, hi⟩ =
        completeSuffixCoverCode (rate := rate) rewards C_star C_h j ⟨source, hj⟩ := by
  intro i j source hi hj
  cases i with
  | none =>
      cases j with
      | none =>
          rfl
      | some s =>
          have hcross : source ∈ launchStartCover (rate := rate) rewards C_star C_h :=
            Set.mem_iUnion.mpr ⟨s, hj⟩
          exact False.elim (hi hcross)
  | some s =>
      cases j with
      | none =>
          have hcross : source ∈ launchStartCover (rate := rate) rewards C_star C_h :=
            Set.mem_iUnion.mpr ⟨s, hi⟩
          exact False.elim (hj hcross)
      | some t =>
          have hstartS : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s.val := by
            change _ ∧ _ at hi
            exact hi.2
          have hstartT : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = t.val := by
            change _ ∧ _ at hj
            exact hj.2
          have hst : s = t := Fin.ext (hstartS.symm.trans hstartT)
          subst t
          rfl

private theorem completeSuffixCoverCode_eq_source (rewards : Rewards p) (C_star C_h : ℝ)
    (tag : Option (Fin (p.T + 1)))
    (source : {source : SourceInput p // source ∈ completeSuffixCover (rate := rate) rewards C_star C_h tag}) :
    completeSuffixCode (rate := rate) rewards C_star C_h source.1 =
      completeSuffixCoverCode (rate := rate) rewards C_star C_h tag source := by
  cases tag with
  | none =>
      have hlaunch := correctedLaunch_eq_none_of_not_mem_launchStartCover
        (rate := rate) rewards C_star C_h source.1 source.2
      simp [completeSuffixCoverCode, completeSuffixCode,
        ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch]
  | some s =>
      exact completeSuffixCode_eq_runObservation (rate := rate) rewards C_star C_h s
        ⟨source.1, source.2⟩

/-- Joint Borel measurability of the literal complete suffix code on the full
original source carrier, including no crossing and a terminal launch. -/
theorem measurable_completeSuffixCode (rewards : Rewards p) (C_star C_h : ℝ) :
    Measurable (fun source : SourceInput p =>
      completeSuffixCode (rate := rate) rewards C_star C_h source) := by
  classical
  let cover := completeSuffixCover (rate := rate) rewards C_star C_h
  let code := completeSuffixCoverCode (rate := rate) rewards C_star C_h
  let compatible := completeSuffixCoverCode_compatible (rate := rate) rewards C_star C_h
  let cover_univ := completeSuffixCover_iUnion_eq_univ (rate := rate) rewards C_star C_h
  have hcover : Measurable (Set.liftCover cover code compatible cover_univ) :=
    measurable_liftCover cover
      (fun tag => measurableSet_completeSuffixCover (rate := rate) rewards C_star C_h tag)
      (fun tag => code tag)
      (fun tag => measurable_completeSuffixCoverCode (rate := rate) rewards C_star C_h tag)
      compatible cover_univ
  have heq : (fun source : SourceInput p =>
      completeSuffixCode (rate := rate) rewards C_star C_h source) =
      Set.liftCover cover code compatible cover_univ := by
    funext source
    by_cases hcross : source ∈ launchStartCover (rate := rate) rewards C_star C_h
    · simp only [launchStartCover, Set.mem_iUnion] at hcross
      obtain ⟨s, hs⟩ := hcross
      rw [Set.liftCover_of_mem (S := cover) (f := code) (hf := compatible)
        (hS := cover_univ) (i := some s) hs]
      exact completeSuffixCoverCode_eq_source (rate := rate) rewards C_star C_h
        (some s) ⟨source, hs⟩
    · rw [Set.liftCover_of_mem (S := cover) (f := code) (hf := compatible)
        (hS := cover_univ) (i := none) hcross]
      exact completeSuffixCoverCode_eq_source (rate := rate) rewards C_star C_h
        none ⟨source, hcross⟩
  rw [heq]
  exact hcover

/-- Joint Borel measurability of the unchanged code list and its existing
coordinator-cell projection. -/
theorem measurable_completeRecorderTrace (rewards : Rewards p) (C_star C_h : ℝ) :
    Measurable (fun source : SourceInput p =>
      completeRecorderTrace (rate := rate) rewards C_star C_h source) := by
  have hcode := measurable_completeSuffixCode (rate := rate) rewards C_star C_h
  have hcells := ReferenceActiveHorizonMeasurability.measurable_list_map
    (records := fun source : SourceInput p =>
      completeSuffixCode (rate := rate) rewards C_star C_h source)
    hcode (ReferenceCoordinatorRecorderCallTrace.cell (p := p) (rate := rate))
    (ReferenceCoordinatorRecorderCallTrace.measurable_cell (p := p) (rate := rate))
  simpa only [completeRecorderTrace] using hcode.prodMk hcells

/-- The code list has exactly one entry for every physical round from the
actual launch boundary through `T-1`. -/
theorem completeSuffixCode_length (rewards : Rewards p) (C_star C_h : ℝ)
    (source : SourceInput p) :
    (completeSuffixCode (rate := rate) rewards C_star C_h source).length =
      p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
  simp only [completeSuffixCode, List.length_map]
  exact ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate source rewards C_star C_h

/-- Code times are exactly the half-open physical interval, including an
empty list when launch is absent or occurs at `T`. -/
theorem completeSuffixCode_times (rewards : Rewards p) (C_star C_h : ℝ)
    (source : SourceInput p) :
    (completeSuffixCode (rate := rate) rewards C_star C_h source).map Prod.fst =
      List.range' (ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h) 1 := by
  unfold completeSuffixCode
  rw [List.map_map]
  change (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).map
      (fun record => (ReferenceActiveHorizonMeasurability.roundRecordCode record).1) = _
  simpa only [ReferenceActiveHorizonMeasurability.roundRecordCode,
    ReferenceActivePhysicalHorizon.calendar] using
    ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values rate source rewards C_star C_h

/-- The trace is exactly the actual records mapped by H, followed by C.cell
on that same mapped list. Every input and option-valued diagnostic is kept. -/
theorem completeRecorderTrace_actualRecords (rewards : Rewards p) (C_star C_h : ℝ)
    (source : SourceInput p) :
    completeRecorderTrace (rate := rate) rewards C_star C_h source =
      let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h
      let codes := records.map
        (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate))
      (codes, codes.map (ReferenceCoordinatorRecorderCallTrace.cell (p := p) (rate := rate))) := rfl

/-- The existing diagnostic projection of one actual code retains precisely
the actual record's recording option. -/
theorem recording_eq_actualDiagnostics
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceCoordinatorRecorderCallTrace.recording
      (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
        record.coordinatorDiagnostics.recording :=
  ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics record

/-- The existing raw coordinator projection is only the option-mapped
recorder diagnostic; it is not asserted to equal a numerical arrival. -/
theorem coordinatorRaw_eq_complementArrival
    (code : RoundRecordCode (p := p) (rate := rate))
    (selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate)
    (j : CanonicalFastSampling.FastArm selected.1.payload.slowSet) :
    ReferenceCoordinatorRecorderCallTrace.coordinatorRaw code j.1 =
      (ReferenceCoordinatorRecorderCallTrace.recording code).map
        (fun output => CoordinatorLiveServiceFinish.complementArrival selected.1.payload output j) :=
  ReferenceCoordinatorRecorderCallTrace.coordinatorRaw_eq_complementArrival code selected j

private abbrev DispatchTailArgs :=
  Unit ⊕ (Unit ⊕ (ReferenceActiveDispatchTemporal.LiveArgs p rate ⊕
    ReferenceActiveDispatchTemporal.CollectionArgs p rate))

private def selectionCodeFromDispatchData
    (data : Fin p.K × (Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
      DispatchTailArgs (p := p) (rate := rate))) :
    Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) :=
  match data.2.1, data.2.2 with
  | some view, Sum.inr (Sum.inr (Sum.inl args)) => some (view, (args.2.2.2, data.1))
  | some view, Sum.inr (Sum.inr (Sum.inr args)) => some (view, (args.2.2.1, data.1))
  | _, _ => none

private theorem selectionCode_eq_of_cutData
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (cut : ReferenceActivePhysicalStep.DispatchCut x) :
    cut.selection.map (ReferenceLiveDispatchOutputMeasurability.encodeSelection) =
      selectionCodeFromDispatchData (ReferenceActiveDispatchTemporal.cutData cut) := by
  classical
  cases cut with
  | first outcome =>
      cases outcome
      all_goals simp_all [selectionCodeFromDispatchData, ReferenceActiveDispatchTemporal.cutData,
          ReferenceActiveDispatchTemporal.tailArgs, ReferenceActivePhysicalStep.DispatchCut.arm,
          ReferenceActivePhysicalStep.DispatchCut.downView,
          ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
          ReferenceLiveDispatchOutputMeasurability.encodeSelection]
      all_goals
        split_ifs <;> simp_all
  | live registers owned base outcome =>
      cases outcome
      all_goals simp_all [selectionCodeFromDispatchData, ReferenceActiveDispatchTemporal.cutData,
          ReferenceActiveDispatchTemporal.tailArgs, ReferenceActivePhysicalStep.DispatchCut.arm,
          ReferenceActivePhysicalStep.DispatchCut.downView,
          ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
          ReferenceLiveDispatchOutputMeasurability.encodeSelection]
  | collection payload ledger clock cutoff outcome =>
      cases outcome
      all_goals simp_all [selectionCodeFromDispatchData, ReferenceActiveDispatchTemporal.cutData,
          ReferenceActiveDispatchTemporal.tailArgs, ReferenceActivePhysicalStep.DispatchCut.arm,
          ReferenceActivePhysicalStep.DispatchCut.downView,
          ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
          ReferenceLiveDispatchOutputMeasurability.encodeSelection]
      all_goals
        split_ifs <;> simp_all
  | invalidCollectionCutoff =>
      simp [selectionCodeFromDispatchData, ReferenceActiveDispatchTemporal.cutData,
        ReferenceActiveDispatchTemporal.tailArgs, ReferenceActivePhysicalStep.DispatchCut.arm,
        ReferenceActivePhysicalStep.DispatchCut.downView, ReferenceActivePhysicalStep.DispatchCut.selection]
  | dagger =>
      simp [selectionCodeFromDispatchData, ReferenceActiveDispatchTemporal.cutData,
        ReferenceActiveDispatchTemporal.tailArgs, ReferenceActivePhysicalStep.DispatchCut.arm,
        ReferenceActivePhysicalStep.DispatchCut.downView, ReferenceActivePhysicalStep.DispatchCut.selection]

private theorem selectionCode_eq_of_dispatchData
    (left right : ReferenceActivePhysicalStep.RoundInput p rate)
    (hdata : ReferenceActiveDispatchTemporal.dispatchData left =
      ReferenceActiveDispatchTemporal.dispatchData right) :
    (ReferenceActivePhysicalStep.dispatch left).selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection =
      (ReferenceActivePhysicalStep.dispatch right).selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection := by
  have hleft := selectionCode_eq_of_cutData (ReferenceActivePhysicalStep.dispatch left)
  have hright := selectionCode_eq_of_cutData (ReferenceActivePhysicalStep.dispatch right)
  rw [hleft, hright]
  exact congrArg selectionCodeFromDispatchData hdata

private theorem firstOutcome_is_chosen (input : CoordinatorRoundDispatch.FirstInput p) :
    ∃ selected,
      CoordinatorRoundDispatch.dispatchFirst input =
        .chosen (CoordinatorAssignmentRegisterInstall.installFirst
          (CoordinatorRoundDispatch.firstLaunchInput input)) selected := by
  classical
  unfold CoordinatorRoundDispatch.dispatchFirst
  extract_lets launch installed started payload weights cutoff hpayload hstarted hcutoff
    hweights hchoice hboundary hnonempty
  split
  · exact False.elim (hnonempty ‹CoordinatorLocalArmChoice.coordinatorArmChoice
      payload started.pending cutoff installed.registers.time weights input.row = none›)
  · rename_i arm hselected
    exact ⟨{
      arm := arm
      choiceInputsValid := hchoice
      recorderBoundaryValid := hboundary
      armChoice_eq := hselected }, rfl⟩

private def firstTailArgs
    (launch : FirstAssignmentLaunch.Input p rate.eta) :
    ReferenceActiveDispatchTemporal.LiveArgs p rate :=
  ⟨(CoordinatorAssignmentRegisterInstall.installFirst launch).registers,
    (CoordinatorAssignmentRegisterInstall.installFirst launch).ownedRegisters,
    ((CoordinatorAssignmentRegisterInstall.installFirst launch).followerBaseScore,
      (CoordinatorAssignmentRegisterInstall.installFirst launch).startRoundResult)⟩

private theorem first_dispatch_tailArgs
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hfirst : x.state.coordinator = .first) :
    ReferenceActiveDispatchTemporal.tailArgs (ReferenceActivePhysicalStep.dispatch x) =
      .inr (.inr (.inl (firstTailArgs
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput x))))) := by
  rw [ReferenceActivePhysicalStep.dispatch_first x hfirst]
  obtain ⟨selection, hchosen⟩ := firstOutcome_is_chosen (ReferenceActivePhysicalStep.firstInput x)
  rw [hchosen]
  have htime :
      (CoordinatorAssignmentRegisterInstall.installFirst
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput x))).registers.time = x.time := rfl
  simp only [ReferenceActiveDispatchTemporal.tailArgs,
    ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt, htime, dite_true, Option.some_ne_none]
  rfl

private theorem dispatchData_eq_of_selected_row
    (state : ReferenceActivePhysicalHorizon.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (time : Fin p.T) (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : Rewards p) (hrow : rows selected = otherRows selected) :
    ReferenceActiveDispatchTemporal.dispatchData
        (⟨state, rows, selected, time, active, rewards⟩ : ReferenceActivePhysicalStep.RoundInput p rate) =
      ReferenceActiveDispatchTemporal.dispatchData
        (⟨state, otherRows, selected, time, active, rewards⟩ : ReferenceActivePhysicalStep.RoundInput p rate) := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, otherRows, selected, time, active, rewards⟩
  change ReferenceActiveDispatchTemporal.cutData (ReferenceActivePhysicalStep.dispatch x) =
    ReferenceActiveDispatchTemporal.cutData (ReferenceActivePhysicalStep.dispatch y)
  cases hphase : state.coordinator with
  | first =>
      have hcurrent : (rows selected).2 time = (otherRows selected).2 time :=
        congrArg (fun row => row.2 time) hrow
      have hpair := ReferenceActiveTemporalCausality.first_dispatch_projections_eq_of_current
        state rows otherRows selected active rewards rewards hphase hcurrent
      have hlaunch := ReferenceActiveTemporalAssembly.firstLaunchInput_eq_of_current
        state rows otherRows selected time active rewards rewards hcurrent
      have htail : ReferenceActiveDispatchTemporal.tailArgs
          (ReferenceActivePhysicalStep.dispatch x) =
        ReferenceActiveDispatchTemporal.tailArgs
          (ReferenceActivePhysicalStep.dispatch y) := by
        rw [first_dispatch_tailArgs x hphase, first_dispatch_tailArgs y hphase]
        exact congrArg (fun args => Sum.inr (Sum.inr (Sum.inl args)))
          (congrArg firstTailArgs hlaunch)
      exact congrArg₂ (fun head tail => (head.1, head.2, tail)) hpair htail
  | live registers owned base =>
      exact ReferenceActiveDispatchTemporal.live_dispatch_data_eq_of_current
        state rows otherRows selected time active rewards rewards registers owned base
        hphase (congrArg (fun row => row.2 time) hrow)
  | collection payload ledger proposal =>
      exact ReferenceActiveDispatchTemporal.collection_dispatch_data_eq_of_current
        state rows otherRows selected time active rewards rewards payload ledger proposal
        hphase (congrArg (fun row => row.2 time) hrow)
  | dagger =>
      rw [ReferenceActivePhysicalStep.dispatch_dagger x hphase,
        ReferenceActivePhysicalStep.dispatch_dagger y hphase]
      rfl

private theorem oneRoundCode_eq_of_input_data
    (left right : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : left.state = right.state) (hselected : left.selected = right.selected)
    (htime : left.time = right.time) (hrewards : left.rewards = right.rewards)
    (hrow : left.row = right.row) :
    ReferenceActiveHorizonMeasurability.roundRecordCode
        ⟨left, ReferenceActivePhysicalStep.step left, rfl⟩ =
      ReferenceActiveHorizonMeasurability.roundRecordCode
        ⟨right, ReferenceActivePhysicalStep.step right, rfl⟩ := by
  rcases left with ⟨leftState, leftRows, leftSelected, leftTime, leftActive, leftRewards⟩
  rcases right with ⟨rightState, rightRows, rightSelected, rightTime, rightActive, rightRewards⟩
  dsimp only at hstate hselected htime hrewards hrow
  cases hstate
  cases hselected
  cases htime
  cases hrewards
  change leftRows leftSelected = rightRows leftSelected at hrow
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨leftState, leftRows, leftSelected, leftTime, leftActive, leftRewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨leftState, rightRows, leftSelected, leftTime, leftActive, leftRewards⟩
  have hdata := dispatchData_eq_of_selected_row (rate := rate)
    leftState leftRows rightRows leftSelected leftTime leftActive leftRewards hrow
  have hcurrent : (leftRows leftSelected).2 leftTime =
      (rightRows leftSelected).2 leftTime := congrArg (fun row => row.2 leftTime) hrow
  have hpast : ∀ s : Fin p.T, s.val < leftTime.val →
      ((leftRows leftSelected).2 s).1 ContinuousControlSlice.Label.prop =
        ((rightRows leftSelected).2 s).1 ContinuousControlSlice.Label.prop := by
    intro s _
    exact congrArg (fun row => (row.2 s).1 ContinuousControlSlice.Label.prop) hrow
  have hevidence := ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
    leftState leftRows rightRows leftSelected leftTime leftActive leftRewards leftRewards
    hcurrent hpast rfl
  have hactions : (ReferenceActivePhysicalStep.prepare x).arms.actions =
      (ReferenceActivePhysicalStep.prepare y).arms.actions := by
    have h := congrArg ReferenceActivePhysicalHorizon.RoundEvidence.actions hevidence
    simpa only [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence,
      ReferenceActivePhysicalHorizon.RoundRecord.actions,
      ReferenceActivePhysicalStep.step] using h
  have hfeedback : (ReferenceActivePhysicalStep.prepare x).feedback.feedback =
      (ReferenceActivePhysicalStep.prepare y).feedback.feedback := by
    have h := congrArg ReferenceActivePhysicalHorizon.RoundEvidence.gridFeedback hevidence
    simpa only [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence,
      ReferenceActivePhysicalHorizon.RoundRecord.gridFeedback,
      ReferenceActivePhysicalStep.step] using h
  have hcoordinator : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
      (ReferenceActivePhysicalStep.prepare y).observeCoordinator := by
    have h := congrArg ReferenceActivePhysicalHorizon.RoundEvidence.coordinator hevidence
    simpa only [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence,
      ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics,
      ReferenceActivePhysicalStep.step] using h
  have hnext : (ReferenceActivePhysicalStep.step x).next =
      (ReferenceActivePhysicalStep.step y).next := by
    have h := congrArg ReferenceActivePhysicalHorizon.RoundEvidence.after hevidence
    simpa only [ReferenceActivePhysicalHorizon.computedEvidence,
      ReferenceActivePhysicalHorizon.RoundRecord.evidence] using h
  have hselection := selectionCode_eq_of_dispatchData x y hdata
  have hdispatchView : (ReferenceActivePhysicalStep.dispatch x).downView =
      (ReferenceActivePhysicalStep.dispatch y).downView := by
    have h := congrArg (fun data : _ => data.2.1) hdata
    simpa only [ReferenceActiveDispatchTemporal.dispatchData,
      ReferenceActiveDispatchTemporal.cutData] using h
  have hphysical :
      ReferenceFirstLiveCoordinatorStepMeasurability.physicalCode x =
        ReferenceFirstLiveCoordinatorStepMeasurability.physicalCode y := by
    unfold ReferenceFirstLiveCoordinatorStepMeasurability.physicalCode
    apply Prod.ext
    · exact hselection
    · apply Prod.ext
      · exact hdispatchView
      · apply Prod.ext
        · exact hactions
        · apply Prod.ext
          · exact hfeedback
          · exact congrArg
              ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation hcoordinator
  have hfollowersCode : ∀ i,
      ReferenceActiveStepCompositionMeasurability.followerObservable x i =
        ReferenceActiveStepCompositionMeasurability.followerObservable y i := by
    intro i
    unfold ReferenceActiveStepCompositionMeasurability.followerObservable
    apply congrArg (ReferenceFollowerTailComposition.finishFollowerObservable rate i
      (leftState.activations i))
    unfold ReferenceFollowerTailComposition.canonicalFollowerInput
    apply Prod.ext
    · exact hdispatchView
    · apply Prod.ext
      · apply congrArg (fun input =>
          FollowerPrepareJointMeasurability.prepareOutputOnInput rate i
            (leftState.activations i) input)
        simp [x, y, ReferenceActivePhysicalStep.RoundInput.row, hrow]
      · exact congrFun hfeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hwhole :
      ReferenceActiveStepCompositionMeasurability.wholeStepCode x =
        ReferenceActiveStepCompositionMeasurability.wholeStepCode y := by
    unfold ReferenceActiveStepCompositionMeasurability.wholeStepCode
    apply Prod.ext
    · exact hphysical
    · apply Prod.ext
      · funext i
        exact hfollowersCode i
      · exact congrArg ReferenceActivePhysicalStepMeasurability.encodeState hnext
  simp only [ReferenceActiveHorizonMeasurability.roundRecordCode, x, y, hwhole]

/-- The existing horizon's code list is invariant under changing unselected
rows. The proof folds the same run and appends its one actual record code on
every coordinator and follower branch. -/
private theorem run_codes_eq_of_selected_row
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : Rewards p) (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hrow : rows selected = otherRows selected) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
        (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) =
      (ReferenceActivePhysicalHorizon.run initial otherRows selected rewards start count hspan hmode).records.map
        (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) := by
  have hfold :
      (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards start start count
        le_rfl hspan hmode ⟨initial, [], rfl, by simp [ReferenceActivePhysicalHorizon.Connected]⟩).finalState =
        (ReferenceActivePhysicalHorizon.foldCalendar initial otherRows selected rewards start start count
          le_rfl hspan hmode ⟨initial, [], rfl, by simp [ReferenceActivePhysicalHorizon.Connected]⟩).finalState ∧
      (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards start start count
        le_rfl hspan hmode ⟨initial, [], rfl, by simp [ReferenceActivePhysicalHorizon.Connected]⟩).records.map
          (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) =
        (ReferenceActivePhysicalHorizon.foldCalendar initial otherRows selected rewards start start count
          le_rfl hspan hmode ⟨initial, [], rfl, by simp [ReferenceActivePhysicalHorizon.Connected]⟩).records.map
          (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) := by
    unfold ReferenceActivePhysicalHorizon.foldCalendar
    refine List.foldl_rel
      (r := fun (left right : ReferenceActivePhysicalHorizon.Run initial) =>
        left.finalState = right.finalState ∧
          left.records.map (ReferenceActiveHorizonMeasurability.roundRecordCode
            (p := p) (rate := rate)) =
            right.records.map (ReferenceActiveHorizonMeasurability.roundRecordCode
              (p := p) (rate := rate)))
      ⟨rfl, rfl⟩ ?_
    intro entry hentry left right hacc
    let x := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards
      start hmode left entry
    let y := ReferenceActivePhysicalHorizon.roundInputAt initial otherRows selected rewards
      start hmode right entry
    have hcurrent : (rows selected).2 x.time = (otherRows selected).2 x.time :=
      congrArg (fun row => row.2 x.time) hrow
    have hpast : ∀ s : Fin p.T, s.val < x.time.val →
        ((rows selected).2 s).1 ContinuousControlSlice.Label.prop =
          ((otherRows selected).2 s).1 ContinuousControlSlice.Label.prop := by
      intro s _
      exact congrArg (fun row => (row.2 s).1 ContinuousControlSlice.Label.prop) hrow
    have hevidence : ReferenceActivePhysicalHorizon.computedEvidence x =
        ReferenceActivePhysicalHorizon.computedEvidence y := by
      let x' : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨x.state, otherRows, selected, x.time, x.active, rewards⟩
      have hlocal : ReferenceActivePhysicalHorizon.computedEvidence x =
          ReferenceActivePhysicalHorizon.computedEvidence x' := by
        change ReferenceActivePhysicalHorizon.computedEvidence
            ⟨x.state, rows, selected, x.time, x.active, rewards⟩ =
          ReferenceActivePhysicalHorizon.computedEvidence
            ⟨x.state, otherRows, selected, x.time, x.active, rewards⟩
        exact ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
          x.state rows otherRows selected x.time x.active rewards rewards hcurrent hpast rfl
      have hcarry : ReferenceActivePhysicalHorizon.computedEvidence x' =
          ReferenceActivePhysicalHorizon.computedEvidence y := by
        exact ReferenceActivePhysicalHorizon.computedEvidence_congr x' y hacc.1 rfl rfl rfl rfl
      exact hlocal.trans hcarry
    have hcode := oneRoundCode_eq_of_input_data (rate := rate) x y hacc.1 rfl rfl rfl hrow
    constructor
    · change (ReferenceActivePhysicalStep.step x).next =
        (ReferenceActivePhysicalStep.step y).next
      exact congrArg ReferenceActivePhysicalHorizon.RoundEvidence.after hevidence
    · change (left.records ++
          [ReferenceActivePhysicalHorizon.RoundRecord.mk x
            (ReferenceActivePhysicalStep.step x) rfl]).map
            (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) =
        (right.records ++
          [ReferenceActivePhysicalHorizon.RoundRecord.mk y
            (ReferenceActivePhysicalStep.step y) rfl]).map
            (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate))
      simp only [List.map_append, List.map_singleton]
      exact congrArg₂ (fun a b : List (RoundRecordCode (p := p) (rate := rate)) => a ++ b)
        hacc.2 (congrArg (fun code => [code]) hcode)
  simpa only [ReferenceActivePhysicalHorizon.run] using hfold.2

/-- Equality of public IDs, every original private array, the original
selected index, and the selected whole row gives equality of observation
codes. Other complete rows may differ; raw history records need not agree. -/
theorem completeSuffixCode_eq_of_source_data (rewards : Rewards p) (C_star C_h : ℝ)
    (source source' : SourceInput p) (j : Fin (M p))
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p source = j)
    (hrow : source.1.2 j = source'.1.2 j) :
    completeSuffixCode (rate := rate) rewards C_star C_h source =
      completeSuffixCode (rate := rate) rewards C_star C_h source' := by
  obtain ⟨_, hboundary, hlaunch⟩ :=
    ReferenceCompletePhysicalHistory.generatedInput_and_launch_eq_of_source_data
      rate source source' rewards C_star C_h j hids hprivate hJ hrow
  by_cases hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none
  · have hnone' : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source' rewards C_star C_h = none := by rw [← hlaunch, hnone]
    simp [completeSuffixCode, ReferenceCompletePhysicalHistory.completeSuffixRecords,
      hnone, hnone']
  · have hnone' : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source' rewards C_star C_h ≠ none := by
      intro h
      apply hnone
      rw [hlaunch, h]
    let active := ReferenceCompletePhysicalHistory.correctedLaunchPayload
      rate source rewards C_star C_h hnone
    let active' := ReferenceCompletePhysicalHistory.correctedLaunchPayload
      rate source' rewards C_star C_h hnone'
    have hactive : active = active' := by
      apply Option.some.inj
      exact (ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
        rate source rewards C_star C_h hnone).symm.trans
        (hlaunch.trans (ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
          rate source' rewards C_star C_h hnone'))
    have hstart : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h =
        ReferenceCompletePhysicalHistory.physicalStart rate source' rewards C_star C_h := by
      simpa only [ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary] using
        congrArg (fun boundary : ReferenceInitializationRun.Boundary p =>
          ReferenceInitializationRun.elapsed p boundary.completed) hboundary
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source' = j := by
      have hscalar : source.2.1.2 = source'.2.1.2 := congrArg (fun e => e.1.2) hprivate
      change PrivateSourceStreams.coordinatorIndex p source'.2.1.2 = j
      rw [← hscalar]
      exact hJ
    have hrow' : source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) =
        source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source') := by
      rw [hJ, hselected]
      exact hrow
    have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) :=
      ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some rate source rewards C_star C_h
        active (ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
          rate source rewards C_star C_h hnone)
    have hmode' : ReferenceActivePhysicalHorizon.allActiveAtStart active'
        (ReferenceCompletePhysicalHistory.physicalStart rate source' rewards C_star C_h) :=
      ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some rate source' rewards C_star C_h
        active' (ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
          rate source' rewards C_star C_h hnone')
    have hspan : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) ≤ p.T := by
      have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h
      omega
    have hstart' : ReferenceCompletePhysicalHistory.physicalStart rate source' rewards C_star C_h =
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := hstart.symm
    rw [← hactive] at hmode'
    have hmodeRight : ReferenceActivePhysicalHorizon.allActiveAtStart active
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) := by
      simpa only [hstart'] using hmode'
    have hrun :
        (ReferenceActivePhysicalHorizon.run active source.1.2 j rewards
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          hspan hmode).records.map
            (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) =
        (ReferenceActivePhysicalHorizon.run active source'.1.2 j rewards
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          hspan hmodeRight).records.map
            (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) := by
      exact run_codes_eq_of_selected_row (rate := rate) active source.1.2 source'.1.2 j rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        hspan hmode hrow
    have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h =
          (ReferenceActivePhysicalHorizon.run active source.1.2 j rewards
            (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            hspan hmode).records := by
      simpa only [hJ, ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.correctedSuffixRun, active] using
        (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate source rewards C_star C_h active
          (ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
            rate source rewards C_star C_h hnone))
    have hrecords' : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source' rewards C_star C_h =
          (ReferenceActivePhysicalHorizon.run active source'.1.2 j rewards
            (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            hspan hmodeRight).records := by
      have hlaunchActive' : ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate source' rewards C_star C_h = some active := by
        exact hlaunch.symm.trans
          (ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
            rate source rewards C_star C_h hnone)
      simpa only [hselected, hstart'] using
        (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate source' rewards C_star C_h active hlaunchActive')
    unfold completeSuffixCode
    rw [hrecords, hrecords']
    exact hrun

/-- The recorder-trace equality follows from equality of the complete code
lists, keeping the same C.cell map. -/
theorem completeRecorderTrace_eq_of_source_data (rewards : Rewards p) (C_star C_h : ℝ)
    (source source' : SourceInput p) (j : Fin (M p))
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p source = j)
    (hrow : source.1.2 j = source'.1.2 j) :
    completeRecorderTrace (rate := rate) rewards C_star C_h source =
      completeRecorderTrace (rate := rate) rewards C_star C_h source' := by
  simpa only [completeRecorderTrace] using congrArg (fun codes =>
    (codes, codes.map (ReferenceCoordinatorRecorderCallTrace.cell (p := p) (rate := rate))))
      (completeSuffixCode_eq_of_source_data (rate := rate) rewards C_star C_h
        source source' j hids hprivate hJ hrow)

/-- Under the original coordinator index, replacing its selected row by the
same complete row gives the same trace. The original scalar and every private
array remain in the source unchanged. -/
theorem completeRecorderTrace_eq_on_selectedRow_update
    (rewards : Rewards p) (C_star C_h : ℝ)
    (ids : CompletePublicTable.IDArray p)
    (rows otherRows : CompletePublicTable.CompleteRows p) (j : Fin (M p))
    (rho : CompletePublicTable.CompleteRow p)
    (e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (hJ : PrivateSourceStreams.coordinatorIndex p e.1.2 = j) :
    completeRecorderTrace (rate := rate) rewards C_star C_h
        ((ids, Function.update rows j rho), e) =
      completeRecorderTrace (rate := rate) rewards C_star C_h
        ((ids, Function.update otherRows j rho), e) := by
  have hrow : (Function.update rows j rho) j = (Function.update otherRows j rho) j := by
    simp
  apply completeRecorderTrace_eq_of_source_data (rate := rate) rewards C_star C_h
    ((ids, Function.update rows j rho), e) ((ids, Function.update otherRows j rho), e) j
  · rfl
  · rfl
  · change PrivateSourceStreams.coordinatorIndex p e.1.2 = j
    exact hJ
  · exact hrow

/-- Fixing the complete public output preserves joint source measurability on
the original private-coordinate carrier. -/
theorem measurable_completeSuffixCode_fixedPublic (rewards : Rewards p) (C_star C_h : ℝ)
    (published : CompletePublicTable.PublishedOutput p) :
    Measurable (fun privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      completeSuffixCode (rate := rate) rewards C_star C_h (published, privateCoords)) := by
  exact (measurable_completeSuffixCode (rate := rate) rewards C_star C_h).comp
    measurable_prodMk_left

/-- The selected-row update section is Borel jointly in the original row
table and the replacement complete row, by Mathlib's measurable update map. -/
theorem measurable_completeSuffixCode_updatedRow (rewards : Rewards p) (C_star C_h : ℝ)
    (ids : CompletePublicTable.IDArray p) (j : Fin (M p))
    (e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    Measurable (fun input : CompletePublicTable.CompleteRows p × CompletePublicTable.CompleteRow p =>
      completeSuffixCode (rate := rate) rewards C_star C_h
        ((ids, Function.update input.1 j input.2), e)) := by
  have hupdate : Measurable (fun input : CompletePublicTable.CompleteRows p ×
      CompletePublicTable.CompleteRow p => Function.update input.1 j input.2) :=
    measurable_update'
  have hpublic : Measurable (fun input : CompletePublicTable.CompleteRows p ×
      CompletePublicTable.CompleteRow p => (ids, Function.update input.1 j input.2)) :=
    measurable_prodMk_left.comp hupdate
  have hsource : Measurable (fun input : CompletePublicTable.CompleteRows p ×
      CompletePublicTable.CompleteRow p => ((ids, Function.update input.1 j input.2), e)) :=
    measurable_prodMk_right.comp hpublic
  exact (measurable_completeSuffixCode (rate := rate) rewards C_star C_h).comp hsource

/-- Fixed-public measurability of the exact coordinator trace. -/
theorem measurable_completeRecorderTrace_fixedPublic (rewards : Rewards p) (C_star C_h : ℝ)
    (published : CompletePublicTable.PublishedOutput p) :
    Measurable (fun privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      completeRecorderTrace (rate := rate) rewards C_star C_h (published, privateCoords)) := by
  exact (measurable_completeRecorderTrace (rate := rate) rewards C_star C_h).comp
    measurable_prodMk_left

/-- Joint updated-row measurability of the exact coordinator trace. -/
theorem measurable_completeRecorderTrace_updatedRow (rewards : Rewards p)
    (C_star C_h : ℝ) (ids : CompletePublicTable.IDArray p) (j : Fin (M p))
    (e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    Measurable (fun input : CompletePublicTable.CompleteRows p × CompletePublicTable.CompleteRow p =>
      completeRecorderTrace (rate := rate) rewards C_star C_h
        ((ids, Function.update input.1 j input.2), e)) := by
  have hupdate : Measurable (fun input : CompletePublicTable.CompleteRows p ×
      CompletePublicTable.CompleteRow p => Function.update input.1 j input.2) :=
    measurable_update'
  have hpublic : Measurable (fun input : CompletePublicTable.CompleteRows p ×
      CompletePublicTable.CompleteRow p => (ids, Function.update input.1 j input.2)) :=
    measurable_prodMk_left.comp hupdate
  have hsource : Measurable (fun input : CompletePublicTable.CompleteRows p ×
      CompletePublicTable.CompleteRow p => ((ids, Function.update input.1 j input.2), e)) :=
    measurable_prodMk_right.comp hpublic
  exact (measurable_completeRecorderTrace (rate := rate) rewards C_star C_h).comp hsource

end Bandits.Support.ReferenceGeneratedCompleteCalendarObservation

end
