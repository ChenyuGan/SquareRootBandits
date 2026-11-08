/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedBirthOutsidePostserviceCut

import Mathlib.Tactic

/-!
# The computed outside queue at the first corrected birth

This module records the native pre-confirmation service result at the actual
first corrected birth.  The projection reads the call retained on the round
record, including when the subsequent coordinator state is the absorbing
dagger.  Its literal overflow event is Borel on the original source, by exact
reconstruction from the accepted installation and recording codes, and is
covered by the existing corrected numerical overflow events.

Sources: ZIP4 `04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:355-361,391-408,425-426`, and
`appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open MeasureTheory
open ConstructorDimensions
open Bandits.Support.ReferenceFirstCollectionCorrectedSliceNumericalPrefix
  (correctedCell sourceRecords birthIndex overflowEvent)
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput)
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration (actualRecord)
open BootstrapPrivateRoundStreams (sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceFirstCollectionCorrectedNumericalOverflowSum (allArmOverflowEvent)

namespace Bandits.Support.ReferenceFirstCorrectedBirthComputedOverflowCover

variable {p : ConstructorDimensions.Parameters}

-- Match the accepted observation carriers for these countable clock fields.
local instance : MeasurableSpace (Option (CoordinatorLocalArmChoice.Cutoff p)) := ⊤
local instance : MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
local instance : MeasurableSpace
    (ReferenceCollectionDispatchMeasurability.ClockObservation p) := ⊤
local instance : MeasurableSpace (CoordinatorPhaseClock.AssignmentStartInstruction p) := ⊤

local notation "X" => SourceInput p

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-- The queue computed by the birth's actual native live service call, before
the confirmation update and finish decision.  It is absent unless the
preparation is the original `.collection/.laterChosen` branch, the arm is in
the installed complement, the retained coordinator recording is present, and
the very same `servicePass` succeeds.  In particular, this reads the retained
call even if the following coordinator configuration is `.dagger`. -/
def preRejectionComputedOutsideQueue (r : Record) (a : Fin p.K) : Option ℕ :=
  match r.output.preparation.coordinator with
  | .collection _ _ _ _
      (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
      if ha : a ∉ installed.registers.payload.slowSet.val then
        match r.output.coordinator.recording with
        | none => none
        | some recording =>
            match CoordinatorLiveServiceFinish.servicePass installed.registers
                installed.ownedRegisters recording with
            | .error _ => none
            | .ok serviced =>
                some (serviced.queue
                  ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩)
      else none
  | _ => none

/-- The first corrected birth's literal event that some actual outside arm's
pre-rejection computed queue crosses the normalized cap. -/
def birthComputedOutsideOverflowEvent (u t : Fin p.T) : Set X :=
  {z | z ∈ correctedCell rate rewards C_star C_h u t ∧
    ∃ birth : Record,
      (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
        some birth ∧
      actualRecord rate rewards C_star C_h t z = some birth ∧
      ∃ a : Fin p.K, ∃ q : ℕ,
        preRejectionComputedOutsideQueue rate birth a = some q ∧
        (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)}

/-- A local observation of the accepted installation code.  This uses the
existing continuous payload carrier and the existing discrete live code. -/
def installedCoordinates? (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    Option (ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate) :=
  ReferenceCollectionOutcomeMeasurability.optionalElim none
    (Sum.elim (fun _ => none) (fun o => o.2.1.map Prod.fst))
    (ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation x)

section

local instance canonicalOptionSpace {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Option α) := LaterAssignmentStartMeasurability.optionMeasurableSpace

theorem measurable_installedCoordinates? :
    Measurable (installedCoordinates? (p := p) rate) := by
  have hm : Measurable (fun o : ReferenceCollectionOutcomeMeasurability.FullObservation p rate =>
      o.2.1.map Prod.fst) :=
    LaterAssignmentFullOutputMeasurability.measurable_optionMap Prod.fst
      measurable_fst
      (fun o : ReferenceCollectionOutcomeMeasurability.FullObservation p rate => o.2.1)
      (measurable_fst.comp measurable_snd)
  have hs : Measurable (Sum.elim (fun _ : Unit =>
      (none : Option (ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate)))
      (fun o : ReferenceCollectionOutcomeMeasurability.FullObservation p rate =>
        o.2.1.map Prod.fst)) := measurable_const.sumElim hm
  have he := ReferenceCollectionOutcomeMeasurability.measurable_optionalElim
    (none : Option (ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate))
    _ hs
  exact he.comp
    ReferenceCollectionOutcomeMeasurability.measurable_canonicalCollectionFullObservation

end

/-- The native service projection on an existing live register bundle.
The actual recording's failure option and the service error are preserved. -/
def queueAtRegisters
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (recording : Option (CoordinatorRecordingOperation.Output p))
    (a : Fin p.K) : Option ℕ :=
  if ha : a ∉ r.payload.slowSet.val then
    match recording with
    | none => none
    | some recording =>
        match CoordinatorLiveServiceFinish.servicePass r owned recording with
        | .error _ => none
        | .ok serviced => some (serviced.queue
            ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩)
  else none

/-- Evaluate the original native service on a decoded installation and the
retained original recording.  No confirmation or finish operation is run. -/
def nativeQueueFromCode
    (code : ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate)
    (recording : Option (CoordinatorRecordingOperation.Output p))
    (a : Fin p.K) : Option ℕ :=
  queueAtRegisters rate
    (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters code.1 code.2)
    (ReferenceActivePhysicalStepMeasurability.decodeLiveOwned code.1 code.2) recording a

/-- Keep the accepted follower carrier folded when expanding the live code.
This is the same runtime reconstruction used by the accepted tail observer. -/
private theorem nativeQueueFromCode_eq_explicit
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (code : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (recording : Option (CoordinatorRecordingOperation.Output p)) (a : Fin p.K) :
    nativeQueueFromCode rate (payload, code) recording a =
      queueAtRegisters rate
        { payload := payload
          priorClock := ⟨code.clockSigma, code.clockCutoff, code.clockBoundary, code.clockProposal⟩
          pendingAtChoice := ReferenceLiveServiceTailMeasurability.pendingFromClockSet code.pending
          time := code.time, gridBoundary := code.gridBoundary
          complementScores := fun j => code.scores j.val }
        { queue := fun j => code.queues j.val
          previousService := fun j => code.previousServices j.val } recording a := rfl

private theorem nativeQueueFromCode_eq_of_control
    (discrete : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (recording : Option (CoordinatorRecordingOperation.Output p)) (a : Fin p.K)
    (P Q : ReferenceActivePhysicalStep.Payload rate)
    (hn : P.n = Q.n) (hslow : P.slowSet = Q.slowSet) :
    nativeQueueFromCode rate (P, discrete) recording a =
      nativeQueueFromCode rate (Q, discrete) recording a := by
  classical
  cases P with
  | mk cap n scale sigma slow anchor pos queues bounds =>
    cases Q with
    | mk cap' n' scale' sigma' slow' anchor' pos' queues' bounds' =>
      dsimp only at hn hslow
      subst n'
      subst slow'
      simp only [nativeQueueFromCode_eq_explicit]
      unfold queueAtRegisters
      dsimp +instances only
      by_cases hout : a ∉ slow.val
      · simp only [dite_eq_left hout]
        cases recording with
        | none => rfl
        | some recording =>
          dsimp +instances only [CoordinatorLiveServiceFinish.servicePass,
            CoordinatorLiveServiceFinish.OwnedRegisters.queueDomainValid,
            CoordinatorLiveServiceFinish.OwnedRegisters.previousServiceDomainValid,
            CoordinatorLiveServiceFinish.complementArrival]
          by_cases hq : ∀ j : CanonicalFastSampling.FastArm slow,
              discrete.queues j.val ≤ p.T * D p
          · simp only [dite_eq_left hq]
            by_cases hp : ∀ j : CanonicalFastSampling.FastArm slow,
                discrete.previousServices j.val ≤ D p
            · simp only [dite_eq_left hp]
              by_cases ha : ∀ j : CanonicalFastSampling.FastArm slow,
                  (if recording.gateArm = some j.val then recording.rawArrival else 0) ≤ D p
              · simp only [dite_eq_left ha]
                by_cases hv : ∀ j : CanonicalFastSampling.FastArm slow,
                    CappedService.service (4 * n) (discrete.queues j.val)
                      (if recording.gateArm = some j.val then recording.rawArrival else 0) ≤ D p
                · simp only [dite_eq_left hv]
                  by_cases hs : ∀ j : CanonicalFastSampling.FastArm slow,
                      discrete.scores j.val + CappedService.service (4 * n) (discrete.queues j.val)
                        (if recording.gateArm = some j.val then recording.rawArrival else 0) ≤ p.T * D p
                  · simp only [dite_eq_left hs]
                    by_cases ho : ∀ j : CanonicalFastSampling.FastArm slow,
                        CappedService.residual (4 * n) (discrete.queues j.val)
                          (if recording.gateArm = some j.val then recording.rawArrival else 0) ≤ p.T * D p
                    · simp only [dite_eq_left ho]
                    · simp only [dite_eq_right ho]
                  · simp only [dite_eq_right hs]
                · simp only [dite_eq_right hv]
              · simp only [dite_eq_right ha]
            · simp only [dite_eq_right hp]
          · simp only [dite_eq_right hq]
      · simp only [dite_eq_right hout]

/-- Native service depends on countable queue/score data, the payload's
integer capacity and slow set, and the finite recording.  Its continuous
anchor remains in the accepted payload Borel space. -/
theorem measurable_nativeQueueFromCode (a : Fin p.K) :
    Measurable (fun z :
      ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate ×
        Option (CoordinatorRecordingOperation.Output p) =>
      nativeQueueFromCode rate z.1 z.2 a) := by
  classical
  let control := fun z :
      ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate ×
        Option (CoordinatorRecordingOperation.Output p) =>
      (z.1.1.n, z.1.1.slowSet, z.1.2, z.2)
  have hp : Measurable (fun z :
      ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate ×
        Option (CoordinatorRecordingOperation.Output p) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hn : Measurable (fun z :
      ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate ×
        Option (CoordinatorRecordingOperation.Output p) => z.1.1.n) :=
    (measurable_fst.comp (comap_measurable
      (LaterAssignmentStartMeasurability.payloadObservation (p := p) (eta := rate.eta)))).comp hp
  have hc : Measurable control := hn.prodMk
    ((ReferenceCollectionDispatchMeasurability.measurable_payloadSlowSet.comp hp).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  intro s hs
  have heq : (fun z => nativeQueueFromCode rate z.1 z.2 a) ⁻¹' s =
      ⋃ b : {b // ∃ z, control z = b ∧ nativeQueueFromCode rate z.1 z.2 a ∈ s},
        control ⁻¹' {b.val} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact ⟨⟨control z, z, rfl, hz⟩, rfl⟩
    · rintro ⟨b, hb⟩
      obtain ⟨y, hy, hys⟩ := b.property
      have hcontrol := hb.trans hy.symm
      dsimp only [control] at hcontrol
      obtain ⟨hn, hslow, hd, hr⟩ := Prod.mk.inj hcontrol |>.imp_right Prod.mk.inj
        |>.imp_right (fun h => h.imp_right Prod.mk.inj)
      change nativeQueueFromCode rate (z.1.1, z.1.2) z.2 a ∈ s
      rw [hd, hr]
      rw [nativeQueueFromCode_eq_of_control rate _ _ a _ _ hn hslow]
      exact hys
  rw [heq]
  exact MeasurableSet.iUnion fun b => hc (measurableSet_singleton b.val)

/-- The original retained recording, read from the existing whole-step code. -/
def inputRecording (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    Option (CoordinatorRecordingOperation.Output p) :=
  (ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1.2.2.2.2.2.2.2.1

theorem measurable_inputRecording : Measurable (inputRecording (p := p) rate) := by
  exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp
        (measurable_fst.comp ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode))))))))

/-- A local code observer of the discarded computation.  Its use below is
restricted to the actual corrected cell, where its installation is proved to
be the same actual later installation. -/
def inputComputedOutsideQueue (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (a : Fin p.K) : Option ℕ :=
  (installedCoordinates? rate x).bind fun code =>
    nativeQueueFromCode rate code (inputRecording rate x) a

theorem measurable_inputComputedOutsideQueue (a : Fin p.K) :
    Measurable (fun x => inputComputedOutsideQueue rate x a) := by
  have hm := ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun z : ReferenceCollectionInstallOutputMeasurability.InstallationCoordinates p rate ×
        ReferenceActivePhysicalStep.RoundInput p rate =>
      nativeQueueFromCode rate z.1 (inputRecording rate z.2) a)
    ((measurable_nativeQueueFromCode rate a).comp
      (measurable_fst.prodMk ((measurable_inputRecording rate).comp measurable_snd)))
    (installedCoordinates? rate) (measurable_installedCoordinates? rate)
  have h := (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim
    (none : Option ℕ) id measurable_id).comp hm
  convert h using 1
  funext x
  unfold inputComputedOutsideQueue
  cases hc : installedCoordinates? rate x <;> simp only [hc, Option.bind_none,
    Option.bind_some, Option.map_none, Option.map_some, Function.comp_apply,
    ReferenceCollectionOutcomeMeasurability.optionalElim, id_eq]

/-- Lossless decoding restores the original service input, not a chosen
witness of a successful service call. -/
theorem nativeQueueFromCode_encode
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (recording : Option (CoordinatorRecordingOperation.Output p)) (a : Fin p.K) :
    nativeQueueFromCode rate
        (r.payload, ReferenceActivePhysicalStepMeasurability.encodeLive r owned base)
        recording a = queueAtRegisters rate r owned recording a := by
  let parts (configuration : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate) :
      Option (ReferenceLiveServiceTailMeasurability.LiveRuntime (p := p) (rate := rate)) :=
    match configuration with
    | .live rv qv basev => some ⟨rv, qv, basev⟩
    | _ => none
  have hparts := congrArg parts
    (ReferenceActivePhysicalStepMeasurability.decodeCoordinator_encodeCoordinator
      (.live r owned base))
  have hdecoded : ReferenceLiveServiceTailMeasurability.decodeLiveRuntime r.payload
      (ReferenceActivePhysicalStepMeasurability.encodeLive r owned base) =
      (⟨r, owned, base⟩ : ReferenceLiveServiceTailMeasurability.LiveRuntime
        (p := p) (rate := rate)) := by
    apply Option.some.inj
    exact hparts
  exact congrArg (fun runtime : ReferenceLiveServiceTailMeasurability.LiveRuntime
      (p := p) (rate := rate) =>
    queueAtRegisters rate runtime.1 runtime.2.1 recording a) hdecoded

/-- The local installation observer returns precisely the installation in
an actual later-choice dispatcher constructor.  All other cases are irrelevant
to this equality and remain unrestricted. -/
theorem installedCoordinates?_actual_collection
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T) :
    match ReferenceActivePhysicalStep.dispatch x with
    | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        installedCoordinates? rate x = some
          (installed.registers.payload,
            ReferenceActivePhysicalStepMeasurability.encodeLive installed.registers
              installed.ownedRegisters installed.retainedBaseScore)
    | _ => True := by
  classical
  open ReferenceCollectionDispatchMeasurability
    ReferenceCollectionInstallOutputMeasurability
    ReferenceCollectionOutcomeMeasurability in
    rw [dispatch_collection x payload ledger proposal hstate hcutoff]
    let b : BoundaryInput p rate :=
      ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time)
    let z := boundaryLocal (⟨b, hcutoff⟩ : {b : BoundaryInput p rate // cutoffValid b})
    change (match ReferenceActivePhysicalStep.DispatchCut.collection payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger proposal
        ⟨ledger.cutoff - 1, by omega⟩) ⟨ledger.cutoff - 1, by omega⟩
      (CoordinatorRoundDispatch.dispatchCollection (assemble z)) with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
          installedCoordinates? rate x = some (installed.registers.payload,
            ReferenceActivePhysicalStepMeasurability.encodeLive installed.registers
              installed.ownedRegisters installed.retainedBaseScore)
      | _ => True)
    generalize hout : CoordinatorRoundDispatch.dispatchCollection (assemble z) = outcome
    cases outcome <;> try trivial
    rename_i core consistent started hstart instruction hi output hlocal clockData installed selected
    obtain ⟨c, hc, hcoords⟩ :=
      ReferenceActiveStepCompositionMeasurability.collection_installed_observation z
        ((installed.registers.payload,
          ReferenceActivePhysicalStepMeasurability.encodeLive installed.registers
            installed.ownedRegisters installed.retainedBaseScore), started)
        (by rw [hout]; rfl)
    have hfull : canonicalCollectionFullObservation x =
        some (.inr (collectionFullObservation z)) := by
      rw [canonicalCollectionFullObservation_collection x payload ledger proposal hstate]
      unfold boundaryFullObservation
      rw [dite_eq_left (show cutoffValid
        ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time) from hcutoff)]
    unfold installedCoordinates?
    rw [hfull]
    simp only [optionalElim, Sum.elim_inr, collectionFullObservation, hc, Option.map_some]
    exact congrArg (fun v => some v.1) hcoords

/-- The recorder field used by the observer is exactly the actual retained
coordinator recording, including on every subsequent failure branch. -/
theorem inputRecording_actual (r : Record) :
    inputRecording rate r.input = r.output.coordinator.recording := by
  have h := congrArg ReferenceActivePhysicalStep.CoordinatorObservation.recording
    (ReferenceActiveStepCompositionMeasurability.wholeStepCode_reconstructs r.input).1
  change inputRecording rate r.input =
    (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.recording at h
  rw [r.output_eq]
  exact h

/-- Original-source observation of the local code at one actual suffix index.
Absence of the original record is kept distinct from a computed zero. -/
def sourceComputedOutsideQueueAt (k : ℕ) (a : Fin p.K) (z : X) : Option ℕ :=
  ((sourceRecords rate rewards C_star C_h z)[k]?).bind fun r =>
    inputComputedOutsideQueue rate r.input a

theorem measurable_sourceComputedOutsideQueueAt (k : ℕ) (a : Fin p.K) :
    Measurable (sourceComputedOutsideQueueAt rate rewards C_star C_h k a) := by
  classical
  let S : Set X := {z | k < (sourceRecords rate rewards C_star C_h z).length}
  have hS : MeasurableSet S :=
    ReferenceCompleteSuffixInputMeasurability.measurableSet_indexDomain
      rate rewards C_star C_h k
  have hon : Measurable (fun z : S => inputComputedOutsideQueue rate
      (ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
        rate rewards C_star C_h k z) a) :=
    (measurable_inputComputedOutsideQueue rate a).comp
      (ReferenceCompleteSuffixInputMeasurability.measurable_actualRoundInputAt
        rate rewards C_star C_h k)
  have hm := Measurable.dite hon (measurable_const (a := (none : Option ℕ))) hS
  convert hm using 1
  funext z
  by_cases hz : z ∈ S
  · simp only [hz, dite_true, sourceComputedOutsideQueueAt,
      List.getElem?_eq_getElem hz, Option.bind_some,
      ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt, List.get_eq_getElem]
    rfl
  · simp only [hz, dite_false, sourceComputedOutsideQueueAt,
      List.getElem?_eq_none (Nat.le_of_not_gt hz), Option.bind_none]

/-- The calendar lookup in the same original suffix, with its real launch
origin and its genuine absent-record branches. -/
def sourceComputedOutsideQueue (t : Fin p.T) (a : Fin p.K) (z : X) : Option ℕ :=
  (actualRecord rate rewards C_star C_h t z).bind fun r =>
    inputComputedOutsideQueue rate r.input a

theorem measurable_sourceComputedOutsideQueue (t : Fin p.T) (a : Fin p.K) :
    Measurable (sourceComputedOutsideQueue rate rewards C_star C_h t a) := by
  classical
  have hs := ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
    rate rewards C_star C_h
  have hi : Measurable (fun z : X => t.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) :=
    (measurable_of_countable (fun n : ℕ => t.val - n)).comp hs
  have hm : Measurable (fun v : ℕ × X =>
      sourceComputedOutsideQueueAt rate rewards C_star C_h v.1 a v.2) :=
    measurable_from_prod_countable_right fun k =>
      measurable_sourceComputedOutsideQueueAt rate rewards C_star C_h k a
  have h : Measurable (fun z : X =>
      if ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val then
        sourceComputedOutsideQueueAt rate rewards C_star C_h
          (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) a z
      else none) := (hm.comp (hi.prodMk measurable_id)).ite
    (measurableSet_le hs (measurable_const (a := t.val)))
    (measurable_const (a := (none : Option ℕ)))
  convert h using 1
  funext z
  unfold sourceComputedOutsideQueue actualRecord
  split_ifs <;> rfl

/-- At the actual corrected birth, every outside coordinate is read from the
same retained recording and the same successful native service pass.  The
remaining clauses are carried through from the accepted producer, including
the source identities, the numerical crossing implication, and all original
confirmation/finish return branches. -/
theorem firstCell_birth_computed_outside_projection
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K) (birth : Record),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = t.val - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z ∧
      c.enabled = true ∧
      (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
        some birth ∧
      actualRecord rate rewards C_star C_h t z = some birth ∧
      birth.input.time = t ∧ birth.input.rows = z.1.2 ∧
      birth.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      birth.input.rewards = rewards ∧
      (match birth.output.preparation.coordinator with
      | .collection _ _ _ _
          (.laterChosen _ _ started _ instruction _ output _ clockData installed _) =>
          instruction.time = t ∧ instruction.kind = .corrected ∧
          installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
          installed.registers.payload = output.payload ∧
          installed.registers.payload.sigma = t ∧
          (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
            (installed.registers.complementScores j, installed.ownedRegisters.queue j) =
              UnstoppedRecordedQueueComparison.unstoppedReplay
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length j.val ∧
            installed.ownedRegisters.previousService j =
              (UnstoppedRecordedQueueComparison.unstoppedReplay
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length j.val).1 -
              (UnstoppedRecordedQueueComparison.unstoppedReplay
                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  (L.take (L.length - 1)) (L.take (L.length - 1)).length j.val).1) ∧
          c.rate = installed.registers.payload.rate ∧
          birth.output.coordinator = ReferenceActivePhysicalStep.livePostChoice
            birth.output.preparation installed.registers installed.ownedRegisters
            installed.retainedBaseScore started ∧
          birth.output.next.coordinator = birth.output.coordinator.configuration ∧
          ∃ (recording : CoordinatorRecordingOperation.Output p)
            (serviced : CoordinatorLiveServiceFinish.ServicedRegisters
              installed.registers installed.ownedRegisters),
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput birth.output.preparation
                installed.registers started) = some recording ∧
            birth.output.coordinator.recording = some recording ∧
            CoordinatorLiveServiceFinish.servicePass installed.registers
              installed.ownedRegisters recording = .ok serviced ∧
            (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
              (serviced.score j, serviced.queue j) =
                UnstoppedRecordedQueueComparison.unstoppedReplay
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  (L ++ [c]) (L ++ [c]).length j.val ∧
              serviced.previousService j =
                (UnstoppedRecordedQueueComparison.unstoppedReplay
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  (L ++ [c]) (L ++ [c]).length j.val).1 -
                (UnstoppedRecordedQueueComparison.unstoppedReplay
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  L L.length j.val).1) ∧
            (∀ a : Fin p.K,
              ∀ ha : a ∉ installed.registers.payload.slowSet.val,
              preRejectionComputedOutsideQueue rate birth a = some
                (serviced.queue
                  ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩)) ∧
            (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
              (serviced.queue j : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val) →
              ∃ d : Fin p.K, z ∈ overflowEvent rate rewards C_star C_h u t d) ∧
            ((CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload
                started.pending
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                birth.input.time birth.input.row
                birth.output.preparation.coordinatorObservation = none ∧
              birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
                birth.input.state.upDecoderBank (.live .confirmationRejected)
                (some recording) none) ∨
             (∃ pending reason,
              CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload
                started.pending
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                birth.input.time birth.input.row
                birth.output.preparation.coordinatorObservation = some pending ∧
              CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time
                started.clock pending birth.input.row = .error reason ∧
              birth.output.coordinator = ReferenceActivePhysicalStep.coordinatorFailure
                birth.input.state.upDecoderBank
                (.live (CoordinatorLiveServiceFinish.finishFailureCode reason))
                (some recording) none) ∨
             (∃ pending finished,
              CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload
                started.pending
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                birth.input.time birth.input.row
                birth.output.preparation.coordinatorObservation = some pending ∧
              CoordinatorPhaseClock.finishRound p rate.eta.val birth.input.time
                started.clock pending birth.input.row = .ok finished ∧
              birth.output.coordinator =
                ⟨.live {
                    payload := installed.registers.payload
                    priorClock := finished.clock
                    pendingAtChoice := finished.pending
                    time := birth.input.time
                    gridBoundary := finished.clock.g
                    complementScores := serviced.score }
                  { queue := serviced.queue
                    previousService := serviced.previousService }
                  installed.retainedBaseScore,
                  birth.input.state.upDecoderBank, none, some recording, none⟩))
      | _ => False) := by
  obtain ⟨L, c, birth, hL, hc, hprefix, hlength, henabled,
      hbirthSource, hactual, hbirthTime, hrows, hselected, hrewards, hprepared⟩ :=
    ReferenceFirstCorrectedBirthOutsidePostserviceCut.firstCell_birth_outside_postservice
      rate rewards C_star C_h u t z hz
  cases hcoord : birth.output.preparation.coordinator <;>
    simp only [hcoord] at hprepared
  rename_i old ledger clock cutoff outcome
  cases outcome <;> simp only at hprepared
  rename_i core consistent started startResult instruction inputInfo output localFrame
    clockData installed selection
  obtain ⟨hinstTime, hkind, hinstall, hpayload, hsigma, hvector,
    hrate, hco, hconfiguration, hreturnCase⟩ := hprepared
  rcases hreturnCase with ⟨recording, serviced, hrun, hdiagRecording, hservice,
    hqueueReplay, hcrossing, hreturns⟩
  refine ⟨L, c, birth, hL, hc, hprefix, hlength, henabled,
    hbirthSource, hactual, hbirthTime, hrows, hselected, hrewards, ?_⟩
  simp only [hcoord]
  refine ⟨hinstTime, hkind, hinstall, hpayload, hsigma, hvector,
    hrate, hco,
    hconfiguration, recording, serviced, hrun, hdiagRecording, hservice,
    hqueueReplay, ?_, hcrossing,
    hreturns⟩
  intro a ha
  simp [preRejectionComputedOutsideQueue, hcoord, hdiagRecording, hservice, ha]

/-- Exact factorization of the physical pre-rejection computation on the
actual corrected cell.  The observer uses the original input and retained
recording, so confirmation rejection, all FINISH errors and the horizon
require no extra survival premise. -/
theorem firstCell_sourceComputedOutsideQueue_eq
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) :
    ∀ a : Fin p.K,
      sourceComputedOutsideQueue rate rewards C_star C_h t a z =
        (actualRecord rate rewards C_star C_h t z).bind
          (fun r => preRejectionComputedOutsideQueue rate r a) := by
  obtain ⟨L, c, birth, hL, hc, hprefix, hlength, henabled,
      hbirth, hactual, htime, hrows, hJ, hrewards, hprepared⟩ :=
    firstCell_birth_computed_outside_projection rate rewards C_star C_h u t z hz
  obtain ⟨n, birth0, theta, hn, ht0, hactual0, hcall, hrows0, hJ0, hrewards0, hearlier⟩ :=
    ReferenceFirstCollectionCurrentNumericalCell.firstCell_record
      rate rewards C_star C_h u t z hz.1
  have he : birth0 = birth := Option.some.inj (hactual0.symm.trans hactual)
  subst birth0
  obtain ⟨old, ledger0, proposal, hstate, hcutoff, hparam⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec birth u theta).mp hcall
  have hbounds : 1 ≤ ledger0.cutoff ∧ ledger0.cutoff ≤ p.T := by
    rw [hcutoff]
    omega
  have hinstalled := installedCoordinates?_actual_collection rate birth.input
    old ledger0 proposal hstate hbounds
  have hprep : birth.output.preparation = ReferenceActivePhysicalStep.prepare birth.input := by
    simpa [ReferenceActivePhysicalStep.step] using
      congrArg (fun o : ReferenceActivePhysicalStep.RoundOutput birth.input => o.preparation)
        birth.output_eq
  have hdispatch : ReferenceActivePhysicalStep.dispatch birth.input =
      birth.output.preparation.coordinator := by
    rw [hprep]
    rfl
  rw [hdispatch] at hinstalled
  cases hcoord : birth.output.preparation.coordinator <;>
    simp only [hcoord] at hprepared
  rename_i old0 ledger clock cutoff outcome
  cases outcome <;> simp only at hprepared
  rename_i core consistent started startResult instruction inputInfo output localFrame
    clockData installed selection
  simp only [hcoord] at hinstalled
  intro a
  simp only [sourceComputedOutsideQueue, hactual, Option.bind_some,
    inputComputedOutsideQueue, hinstalled, inputRecording_actual]
  dsimp only [Option.bind]
  let rv : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta := installed.registers
  let qv : CoordinatorLiveServiceFinish.OwnedRegisters rv := installed.ownedRegisters
  let bv : Fin (p.m - 1) → ℕ := installed.retainedBaseScore
  change nativeQueueFromCode rate
    (rv.payload, ReferenceActivePhysicalStepMeasurability.encodeLive rv qv bv) birth.output.coordinator.recording a =
    preRejectionComputedOutsideQueue rate birth a
  rw [nativeQueueFromCode_encode rate rv qv bv]
  unfold queueAtRegisters
  simp only [preRejectionComputedOutsideQueue, hcoord]
  cases hr : birth.output.coordinator.recording with
  | none => split_ifs <;> rfl
  | some recording =>
      dsimp only
      cases hs : CoordinatorLiveServiceFinish.servicePass rv qv recording with
      | error reason =>
          have hs0 : CoordinatorLiveServiceFinish.servicePass installed.registers
              installed.ownedRegisters recording = .error reason := hs
          split_ifs <;> simp only [hs0]
      | ok serviced =>
          let serviced0 : CoordinatorLiveServiceFinish.ServicedRegisters
              installed.registers installed.ownedRegisters := serviced
          have hs0 : CoordinatorLiveServiceFinish.servicePass installed.registers
              installed.ownedRegisters recording = .ok serviced0 := hs
          split_ifs <;> simp only [hs0]
          rfl

/-- Whenever the birth returns a stored outside register, it is precisely
the pre-rejection computation.  Rejected confirmations and every failed
FINISH have absent storage, while the earlier projection remains available. -/
theorem firstCell_birth_computed_eq_stored_of_present
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) :
    ∃ birth : Record,
      (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
        some birth ∧
      actualRecord rate rewards C_star C_h t z = some birth ∧
      ∀ (a : Fin p.K) (q : ℕ),
        ReferenceFirstCollectionCorrectedStoredOutsideOverflowCover.storedOutsideQueue
          rate birth a = some q →
        preRejectionComputedOutsideQueue rate birth a = some q := by
  obtain ⟨L, c, birth, hL, hc, hprefix, hlength, henabled,
      hbirth, hactual, htime, hrows, hJ, hrewards, hprepared⟩ :=
    firstCell_birth_computed_outside_projection rate rewards C_star C_h u t z hz
  refine ⟨birth, hbirth, hactual, ?_⟩
  cases hcoord : birth.output.preparation.coordinator <;>
    simp only [hcoord] at hprepared
  rename_i old ledger clock cutoff outcome
  cases outcome <;> simp only at hprepared
  rename_i core consistent started startResult instruction inputInfo output localFrame
    clockData installed selection
  obtain ⟨hinstTime, hkind, hinstall, hpayload, hsigma, hvector, hrate, hco,
    hconfiguration, recording, serviced, hrun, hdiag, hservice, hreplay, hprojection,
    hcross, hreturns⟩ := hprepared
  rcases hreturns with ⟨hconfirm, hfailure⟩ |
      ⟨pending, reason, hconfirm, hfinish, hfailure⟩ |
      ⟨pending, finished, hconfirm, hfinish, hsuccess⟩
  · intro a q hstored
    simp only [ReferenceFirstCollectionCorrectedStoredOutsideOverflowCover.storedOutsideQueue,
      hconfiguration, hfailure, ReferenceActivePhysicalStep.coordinatorFailure] at hstored
    cases hstored
  · intro a q hstored
    simp only [ReferenceFirstCollectionCorrectedStoredOutsideOverflowCover.storedOutsideQueue,
      hconfiguration, hfailure, ReferenceActivePhysicalStep.coordinatorFailure] at hstored
    cases hstored
  · intro a q hstored
    simp only [ReferenceFirstCollectionCorrectedStoredOutsideOverflowCover.storedOutsideQueue,
      hconfiguration, hsuccess] at hstored
    split_ifs at hstored with ha
    · exact (hprojection a ha).trans hstored

/-- The source-record and calendar lookups in the literal event are removed
only by this exact same-source characterization. -/
theorem birthComputedOutsideOverflowEvent_eq_observed (u t : Fin p.T) :
    birthComputedOutsideOverflowEvent rate rewards C_star C_h u t =
      correctedCell rate rewards C_star C_h u t ∩
        {z | ∃ a : Fin p.K, ∃ q : ℕ,
          sourceComputedOutsideQueue rate rewards C_star C_h t a z = some q ∧
          (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)} := by
  ext z
  constructor
  · rintro ⟨hz, birth, hbirth, hactual, a, q, hq, hthreshold⟩
    refine ⟨hz, a, q, ?_, hthreshold⟩
    rw [firstCell_sourceComputedOutsideQueue_eq rate rewards C_star C_h u t z hz a,
      hactual, Option.bind_some]
    exact hq
  · rintro ⟨hz, a, q, hq, hthreshold⟩
    obtain ⟨L, c, birth, hL, hc, hprefix, hlength, henabled,
        hbirth, hactual, htime, hrows, hJ, hrewards, hprepared⟩ :=
      firstCell_birth_computed_outside_projection rate rewards C_star C_h u t z hz
    refine ⟨hz, birth, hbirth, hactual, a, q, ?_, hthreshold⟩
    rw [firstCell_sourceComputedOutsideQueue_eq rate rewards C_star C_h u t z hz a,
      hactual, Option.bind_some] at hq
    exact hq

/-- Original-source Borelness of the literal discarded-birth queue event.
Only the existing canonical input/installation/recording codes and finite or
countable lookups are used; no continuous payload is made discrete. -/
theorem measurableSet_birthComputedOutsideOverflowEvent (u t : Fin p.T) :
    MeasurableSet (birthComputedOutsideOverflowEvent rate rewards C_star C_h u t) := by
  rw [birthComputedOutsideOverflowEvent_eq_observed]
  apply (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurableSet_correctedCell
    rate rewards C_star C_h u t).inter
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro q
  by_cases hq : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)
  · simp only [hq, and_true]
    exact measurableSet_eq_fun
      (measurable_sourceComputedOutsideQueue rate rewards C_star C_h t a)
      (measurable_const (a := some q))
  · simp only [hq, and_false, Set.ofPred_false]
    exact MeasurableSet.empty

/-- The computed birth crossing is covered by the existing numerical union;
the detecting arm is the service-pass coordinate supplied by the producer. -/
theorem birthComputedOutsideOverflowEvent_subset_allArmOverflowEvent
    (u t : Fin p.T) :
    birthComputedOutsideOverflowEvent rate rewards C_star C_h u t ⊆
      ⋃ a : Fin p.K, overflowEvent rate rewards C_star C_h u t a := by
  intro z hzEvent
  obtain ⟨hz, birth, hbirthSource, hactual, a, q, hprojection, hthreshold⟩ := hzEvent
  obtain ⟨L, c, birth0, hL, hc, hprefix, hlength, henabled,
      hbirthSource0, hactual0, hbirthTime, hrows, hselected, hrewards, hprepared⟩ :=
    firstCell_birth_computed_outside_projection rate rewards C_star C_h u t z hz
  have hbirthEq : birth0 = birth := Option.some.inj (hbirthSource0.symm.trans hbirthSource)
  subst birth0
  cases hcoord : birth.output.preparation.coordinator <;>
    simp only [hcoord] at hprepared
  rename_i old ledger clock cutoff outcome
  cases outcome <;> simp only at hprepared
  rename_i core consistent started startResult instruction inputInfo output localFrame
    clockData installed selection
  obtain ⟨_, _, _, _, _, _, _, _, _, recording, serviced, _, _, _, _, hprojectionAll,
    hcrossing, _hreturns⟩ := hprepared
  have ha : a ∉ installed.registers.payload.slowSet.val := by
    simp only [preRejectionComputedOutsideQueue, hcoord] at hprojection
    split_ifs at hprojection with houtside
    · exact houtside
  let j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet :=
    ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩
  have hprojection' :
      preRejectionComputedOutsideQueue rate birth a = some (serviced.queue j) := by
    simpa only [j] using hprojectionAll a ha
  have hq : q = serviced.queue j := Option.some.inj (hprojection.symm.trans hprojection')
  obtain ⟨d, hd⟩ := hcrossing j (by simpa only [hq] using hthreshold)
  exact Set.mem_iUnion.mpr ⟨d, hd⟩

/-- The local birth event is contained in the accepted all-arm, all-cell
corrected numerical overflow union under the unchanged original source law. -/
theorem birthComputedOutsideOverflowEvent_subset_numericalOverflowSum
    (u t : Fin p.T) :
    birthComputedOutsideOverflowEvent rate rewards C_star C_h u t ⊆
      allArmOverflowEvent rate rewards C_star C_h := by
  intro z hz
  have harm := birthComputedOutsideOverflowEvent_subset_allArmOverflowEvent
    rate rewards C_star C_h u t hz
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp harm
  exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨u,
    Set.mem_iUnion.mpr ⟨t, ha⟩⟩⟩

/-- The union over every corrected birth cell is covered by the same accepted
numerical event family; no source-law or inherited-energy reset is made. -/
def allBirthComputedOutsideOverflowEvent : Set X :=
  ⋃ u : Fin p.T, ⋃ t : Fin p.T,
    birthComputedOutsideOverflowEvent rate rewards C_star C_h u t

theorem measurableSet_allBirthComputedOutsideOverflowEvent :
    MeasurableSet (allBirthComputedOutsideOverflowEvent rate rewards C_star C_h) :=
  MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun t =>
    measurableSet_birthComputedOutsideOverflowEvent rate rewards C_star C_h u t

theorem allBirthComputedOutsideOverflowEvent_subset_numericalOverflowSum :
    allBirthComputedOutsideOverflowEvent rate rewards C_star C_h ⊆
      allArmOverflowEvent rate rewards C_star C_h := by
  intro z hz
  obtain ⟨u, hz⟩ := Set.mem_iUnion.mp hz
  obtain ⟨t, hz⟩ := Set.mem_iUnion.mp hz
  exact birthComputedOutsideOverflowEvent_subset_numericalOverflowSum
    rate rewards C_star C_h u t hz

/-- Per corrected cell, the original-law measure is bounded by the
existing exact all-arm corrected numerical overflow estimate. -/
theorem birthComputedOutsideOverflowEvent_measure_le
    (control0 : TimeControl p) (u t : Fin p.T) :
    (sourceInputLaw p).real
        (birthComputedOutsideOverflowEvent rate rewards C_star C_h u t) ≤
      2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) := by
  calc
    (sourceInputLaw p).real
        (birthComputedOutsideOverflowEvent rate rewards C_star C_h u t) ≤
      (sourceInputLaw p).real (allArmOverflowEvent rate rewards C_star C_h) :=
        MeasureTheory.measureReal_mono
          (birthComputedOutsideOverflowEvent_subset_numericalOverflowSum
            rate rewards C_star C_h u t) (by finiteness)
    _ ≤ 2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) :=
      ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent_measure_le
        rate rewards C_star C_h control0

/-- The all-cell union has the same unchanged original-law estimate from the
accepted numerical overflow sum. -/
theorem allBirthComputedOutsideOverflowEvent_measure_le
    (control0 : TimeControl p) :
    (sourceInputLaw p).real
        (allBirthComputedOutsideOverflowEvent rate rewards C_star C_h) ≤
      2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) := by
  calc
    (sourceInputLaw p).real
        (allBirthComputedOutsideOverflowEvent rate rewards C_star C_h) ≤
      (sourceInputLaw p).real (allArmOverflowEvent rate rewards C_star C_h) :=
        MeasureTheory.measureReal_mono
          (allBirthComputedOutsideOverflowEvent_subset_numericalOverflowSum
            rate rewards C_star C_h) (by finiteness)
    _ ≤ 2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) :=
      ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent_measure_le
        rate rewards C_star C_h control0

end Bandits.Support.ReferenceFirstCorrectedBirthComputedOverflowCover

end
