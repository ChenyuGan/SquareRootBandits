/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionInstallOutputMeasurability

/-!
# Complete deterministic collection dispatch observations

Sources: `sources/zip4/manuscript/06_interruptions.tex:30-70,235-260` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,46-64`.

The joint Borel observation retains complete continuous later output plus
literal reconstruction registers. Its decoder restores numerical fields from
stored coordinates; original inputs supply indices and proof certificates.
Step/horizon, physical truth, sampling laws and regret remain open.

Sole direct project dependency: ReferenceCollectionInstallOutputMeasurability,
SHA-256 f5230f2d1d9388d6330bfd30c43cd9e9b6b126bc8574ed865d88ac82ec89246e.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCollectionOutcomeMeasurability

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalStepMeasurability
open Bandits.Support.ReferenceCollectionDispatchMeasurability
open Bandits.Support.ReferenceCollectionInstallOutputMeasurability

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters} {rate : RateInput p}

local instance : MeasurableSpace (Option (CoordinatorLocalArmChoice.Cutoff p)) := ⊤
local instance : MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
local instance : MeasurableSpace (ReferenceCollectionDispatchMeasurability.ClockObservation p) := ⊤
local instance : DiscreteMeasurableSpace (ReferenceCollectionDispatchMeasurability.ClockObservation p) :=
  ⟨fun _ => trivial⟩
local instance : MeasurableSpace (CoordinatorPhaseClock.AssignmentStartInstruction p) := ⊤
local instance : DiscreteMeasurableSpace (CoordinatorPhaseClock.AssignmentStartInstruction p) :=
  ⟨fun _ => trivial⟩

local instance optionDiscrete {A : Type*} [MeasurableSpace A] [DiscreteMeasurableSpace A] :
    DiscreteMeasurableSpace (Option A) := by
  constructor
  intro s
  let e := Equiv.optionEquivSumPUnit A
  exact ⟨e '' s, measurableSet_sum_iff.mpr
    ⟨MeasurableSet.of_discrete, MeasurableSet.of_discrete⟩, e.injective.preimage_image s⟩

/-- Apply a measurable map to an optional value and an independent original
input. The Option sigma algebra is the accepted sum-induced one. -/
def mapOptional {A B C : Type*} (f : A × B → C) (z : Option A × B) : Option C :=
  z.1.map fun a => f (a, z.2)
theorem measurable_mapOptional {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (f : A × B → C) (hf : Measurable f) : Measurable (mapOptional f) := by
  exact measurable_optionMapDependent
    (fun q : A × (Option A × B) => f (q.1, q.2.2))
    (hf.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
    Prod.fst measurable_fst

/-- Eliminate an Option using its ordinary sum-induced measurable space. -/
def optionalElim {A B : Type*} (b : B) (f : A → B) : Option A → B
  | none => b
  | some a => f a
theorem measurable_optionalElim {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (b : B) (f : A → B) (hf : Measurable f) : Measurable (optionalElim b f) := by
  have h : Measurable (Sum.elim f (fun _ : PUnit => b)) :=
    measurable_fun_sum hf measurable_const
  have hm := h.comp (comap_measurable (Equiv.optionEquivSumPUnit A))
  convert hm using 1
  funext a
  cases a <;> rfl

/-- Omit only the certificates of the existing Selection. -/
def selectionFromCandidate (c : ContinuingObservation p rate) : Option (SelectionCoordinates p rate) :=
  c.2.2.map fun arm => (c.1, c.2.1, arm)
theorem measurable_selectionFromCandidate :
    Measurable (selectionFromCandidate (p := p) (rate := rate)) := by
  have h : Measurable (fun q : ContinuingObservation p rate × Option (Fin p.K) =>
      q.2.map fun arm => (q.1.1, q.1.2.1, arm)) := by
    apply measurable_from_prod_countable_left
    intro arm
    cases arm with
    | none => exact measurable_const
    | some arm =>
        have hf : Measurable (fun c : ContinuingObservation p rate => (c.1, c.2.1, arm)) :=
          measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk measurable_const)
        exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ hf
  exact h.comp (measurable_id.prodMk (measurable_snd.comp measurable_snd))

private def failureIndex : CoordinatorRoundDispatch.CollectionFailure → Fin 7
  | .stateDomainFailure => 0
  | .currentScoreDomainFailure => 1
  | .wrongClockBranch => 2
  | .choiceDomainFailure => 3
  | .recorderBoundaryFailure => 4
  | .choiceRejected => 5
  | .assignmentInstructionMissing => 6

private theorem failureIndex_injective : Function.Injective failureIndex := by
  intro a b h
  cases a <;> cases b <;> simp_all [failureIndex]

local instance : Countable CoordinatorRoundDispatch.CollectionFailure := failureIndex_injective.countable
local instance : MeasurableSpace CoordinatorRoundDispatch.CollectionFailure := ⊤

/-- All final tags. Later failure codes distinguish reconstruction, prefix
arm/reason, and orientation set without translating any failure payload. -/
inductive CollectionTag (p : Parameters) where
  | clockFailure
  | localFailure (reason : CoordinatorRoundDispatch.CollectionFailure)
  | coreFailure (reason : CoordinatorRoundDispatch.CollectionFailure)
  | continuing
  | laterFailure (code : LaterAssignmentStartMeasurability.LaterAssignmentStartCode p)
  | laterChoiceFailure (reason : CoordinatorRoundDispatch.CollectionFailure)
  | laterChosen
  deriving Countable, DecidableEq

instance : MeasurableSpace (CollectionTag p) := ⊤
instance : DiscreteMeasurableSpace (CollectionTag p) := ⟨fun _ => trivial⟩

/-- A countable decision key, after all continuous observations have been
proved Borel. Neither a payload nor a row nor a real weight occurs in it. -/
abbrev TagKey (p : Parameters) := ClockObservation p × (Bool × (Bool × (Bool ×
  (Option (Option (Fin p.K)) ×
    (Option (LaterAssignmentStartMeasurability.LaterAssignmentStartCode p) ×
      Option (Bool × (Bool × (Bool × (Bool × Option (Fin p.K))))))))))

def tagFromKey (k : TagKey p) : CollectionTag p :=
  match k.1 with
  | .inl _ => .clockFailure
  | .inr started =>
      if k.2.1 then
        if k.2.2.1 then
          if k.2.2.2.1 then
            match k.2.2.2.2.1 with
            | some (some _) => .continuing
            | _ => .coreFailure .choiceDomainFailure
          else .coreFailure .currentScoreDomainFailure
        else
          match started.assignmentStart with
          | none => .coreFailure .assignmentInstructionMissing
          | some _ => match k.2.2.2.2.2.1 with
            | none => .coreFailure .stateDomainFailure
            | some (.sampled _) => match k.2.2.2.2.2.2 with
              | some (false, _) => .laterChoiceFailure .stateDomainFailure
              | some (true, false, _) => .laterChoiceFailure .choiceDomainFailure
              | some (true, true, false, _) => .laterChoiceFailure .recorderBoundaryFailure
              | some (true, true, true, false, _) => .laterChoiceFailure .recorderBoundaryFailure
              | some (true, true, true, true, some _) => .laterChosen
              | _ => .laterChoiceFailure .choiceRejected
            | some code => .laterFailure code
      else .localFailure .stateDomainFailure

def tagKey (z : LocalInput p rate) : TagKey p :=
  (clockObservation z, coreCheck z, decide (assemble z).ledger.pending.Nonempty,
    CoordinatorRoundDispatch.collectionCurrentScoresCheck (assemble z),
    (continuingObservation? z).map (fun c => c.2.2),
    (laterObservation? z).map (fun c => c.1),
    (laterInstalledObservation? z).map (fun c => c.2.2.2))
theorem measurable_tagKey : Measurable (tagKey (p := p) (rate := rate)) := by
  have hpending : Measurable (fun z : LocalInput p rate => decide z.2.1.pending.Nonempty) :=
    (measurable_of_countable (fun l : Ledger rate => decide l.pending.Nonempty)).comp
      (measurable_fst.comp measurable_snd)
  exact measurable_clockObservation.prodMk (measurable_coreCheck.prodMk
    (hpending.prodMk (measurable_currentScoresCheck.prodMk
      ((LaterAssignmentFullOutputMeasurability.measurable_optionMap _
        (measurable_snd.comp measurable_snd) _ measurable_continuingObservation?).prodMk
      ((LaterAssignmentFullOutputMeasurability.measurable_optionMap _ measurable_fst _
        measurable_laterObservation?).prodMk
      (LaterAssignmentFullOutputMeasurability.measurable_optionMap _
        (measurable_snd.comp (measurable_snd.comp measurable_snd)) _
        measurable_laterInstalledObservation?))))))

def collectionTag (z : LocalInput p rate) : CollectionTag p := tagFromKey (tagKey z)
theorem measurable_collectionTag : Measurable (collectionTag (p := p) (rate := rate)) :=
  (measurable_of_countable tagFromKey).comp measurable_tagKey

/-- Read the view, original clock result, and guarded arm from I's complete code. -/
def installedCandidate (c : InstalledObservation p rate) : ContinuingObservation p rate :=
  (c.2.1, c.2.2.1, c.2.2.2.2.2.2.2)
theorem measurable_installedCandidate : Measurable
    (installedCandidate (p := p) (rate := rate)) :=
  (measurable_fst.comp measurable_snd).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))))))

/-- Selected view, clock and arm from the Borel producer observations. -/
def collectionSelectionCode (z : LocalInput p rate) : Option (SelectionCoordinates p rate) :=
  if collectionTag z = .continuing then
    optionalElim none selectionFromCandidate (continuingObservation? z)
  else if collectionTag z = .laterChosen then
    optionalElim none (fun c => selectionFromCandidate (installedCandidate c)) (laterInstalledObservation? z)
  else none
theorem measurable_collectionSelectionCode :
    Measurable (collectionSelectionCode (p := p) (rate := rate)) := by
  classical
  exact Measurable.ite (measurableSet_eq_fun measurable_collectionTag measurable_const)
    ((measurable_optionalElim _ _ measurable_selectionFromCandidate).comp
      measurable_continuingObservation?)
    (Measurable.ite (measurableSet_eq_fun measurable_collectionTag measurable_const)
      ((measurable_optionalElim _ _ (measurable_selectionFromCandidate.comp measurable_installedCandidate)).comp measurable_laterInstalledObservation?)
      measurable_const)

/-- Literal optional cutoff/current registers. These natural-valued fields
retain absence as well as every score, queue and previous service. -/
abbrev RegisterObservation (p : Parameters) :=
  (Fin p.K → Option (ℕ × (ℕ × ℕ))) × (Fin p.K → Option (ℕ × ℕ))

def registerObservation (z : LocalInput p rate) : RegisterObservation p :=
  (fun a => (z.2.1.cutoffRegisters a).map (fun r => (r.score, r.queue, r.lastService)),
    fun a => (z.2.1.currentRegisters a).map (fun r => (r.queue, r.lastService)))
theorem measurable_registerObservation :
    Measurable (registerObservation (p := p) (rate := rate)) :=
  (measurable_of_countable (fun l : Ledger rate =>
    (((fun a => (l.cutoffRegisters a).map (fun r : CoordinatorCollectionLedger.CutoffRegister =>
      (r.score, r.queue, r.lastService))), fun a => (l.currentRegisters a).map
        (fun r : CoordinatorCollectionLedger.CurrentRegister => (r.queue, r.lastService))) :
          RegisterObservation p))).comp
    (measurable_fst.comp measurable_snd)

/-- Joint prefix, installation, final tag, selection and reconstruction registers;
all continuous fibers keep their inherited Borel spaces. -/
abbrev FullObservation (p : Parameters) (rate : RateInput p) :=
  CollectionPrefixObservation p rate ×
    (Option (InstalledObservation p rate) ×
      (CollectionTag p × (Option (SelectionCoordinates p rate) × RegisterObservation p)))

def collectionFullObservation (z : LocalInput p rate) : FullObservation p rate :=
  (collectionPrefixObservation z, laterInstalledObservation? z,
    collectionTag z, collectionSelectionCode z, registerObservation z)
theorem measurable_collectionFullObservation :
    Measurable (collectionFullObservation (p := p) (rate := rate)) :=
  measurable_collectionPrefixObservation.prodMk
    (measurable_laterInstalledObservation?.prodMk
      (measurable_collectionTag.prodMk
        (measurable_collectionSelectionCode.prodMk measurable_registerObservation)))

theorem later_code_observed (z : CoreInput p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z.val).time
      (assemble z.val).clock (assemble z.val).ledger.pending = .ok started)
    (hpending : ¬ z.val.2.1.pending.Nonempty)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hi : started.assignmentStart = some instruction) :
    (laterObservation? z.val).map (fun c => c.1) =
      some (LaterAssignmentStartMeasurability.codeOfResult p
        (LaterAssignmentStartOperation.laterAssignmentStart z.val.1.1
          (operationLedger z) instruction z.val.1.2 (localConsistency z))) := by
  have hrequest : requestedInstruction z.val = some instruction := by
    simp only [requestedInstruction, requestedInstructionAt, ite_eq_right hpending,
      clockObservation, hstart, hi]
  rw [laterObservation?_of_instruction z.val z.property instruction hrequest]
  rfl

/-- Literal final tag of the original dependent outcome. Clock reasons and
StartRound data are retained separately in the full clock observation. -/
def outcomeTag {x : CoordinatorRoundDispatch.CollectionInput p} :
    CoordinatorRoundDispatch.CollectionOutcome x → CollectionTag p
  | .clockFailure _ _ => .clockFailure
  | .localFailure _ _ _ reason => .localFailure reason
  | .coreFailure _ _ _ reason => .coreFailure reason
  | .continuing _ _ _ _ => .continuing
  | .laterReconstructionFailure _ _ _ _ _ _ reason _ =>
      .laterFailure (.reconstructionFailure reason)
  | .laterPrefixFailure _ _ _ _ _ _ arm reason _ => .laterFailure (.prefixFailure arm reason)
  | .laterOrientationFailure _ _ _ _ _ _ set _ => .laterFailure (.orientationFailure set)
  | .laterChoiceFailure _ _ _ _ _ _ _ _ _ _ reason => .laterChoiceFailure reason
  | .laterChosen _ _ _ _ _ _ _ _ _ _ _ => .laterChosen

/-- Restore a continuing snapshot from its retained clock and arm. All
remaining fields are certificates; the numerical weights remain the original
cutoff-score-plus-increment weights. -/
def restorePrepared (z : CoreInput p rate)
    (hpending : z.val.2.1.pending.Nonempty)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z.val).time
      (assemble z.val).clock (assemble z.val).ledger.pending = .ok started)
    (arm : Fin p.K)
    (hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid (assemble z.val).payload
      (some (CoordinatorCollectionUpRoundStep.localCutoff (assemble z.val).cutoffIndex))
      (assemble z.val).time (CoordinatorCollectionInteractive.PreObservationInputs.weights
        (assemble z.val) z.property.ledger_valid z.property.assignment_eq))
    (hselected : CoordinatorLocalArmChoice.coordinatorArmChoice (assemble z.val).payload
      started.pending
      (some (CoordinatorCollectionUpRoundStep.localCutoff (assemble z.val).cutoffIndex))
      (assemble z.val).time (CoordinatorCollectionInteractive.PreObservationInputs.weights
        (assemble z.val) z.property.ledger_valid z.property.assignment_eq)
      (assemble z.val).row = some arm) :
    CoordinatorCollectionInteractive.PreparedSnapshot (assemble z.val) := by
  have heq : started = carriedStart ⟨z, hpending⟩ :=
    Except.ok.inj (hstart.symm.trans (carriedStart_eq_actual ⟨z, hpending⟩))
  exact {
    inputsValid := {
      ledger_valid := z.property.ledger_valid
      ledger_ready := z.property.ledger_ready
      pending_nonempty := hpending
      assignment_eq := z.property.assignment_eq
      base_score_eq := z.property.base_score_eq
      clock_parameter_valid := z.property.clock_parameter_valid
      clock_registers_valid := z.property.clock_registers_valid
      clock_start_time_valid := z.property.clock_start_time_valid
      clock_sigma_eq := z.property.clock_sigma_eq
      clock_cutoff_eq := z.property.clock_cutoff_eq
      ledger_sigma_eq := z.property.ledger_sigma_eq
      ledger_cutoff_eq := z.property.ledger_cutoff_eq
      ledger_freeze_eq := z.property.ledger_freeze_eq
      ledger_cursor_eq := z.property.ledger_cursor_eq
      decoder_bank_valid := z.property.decoder_bank_valid
      choice_valid := hchoice }
    clockStarted := started
    clockStarted_eq := hstart
    clockStarted_frame := by rw [heq]; exact ⟨rfl, rfl, rfl, rfl⟩
    arm := arm
    armChoice_eq := hselected }

/-- Recover the equation of the retained original clock failure. -/
theorem clockObservation_error (z : LocalInput p rate)
    (failure : CoordinatorPhaseClock.ClockFailure)
    (hclock : clockObservation z = .inl failure) :
    CoordinatorPhaseClock.startRound p rate.eta.val (assemble z).time
      (assemble z).clock (assemble z).ledger.pending = .error failure := by
  cases h : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z).time
      (assemble z).clock (assemble z).ledger.pending with
  | error reason =>
      simp only [clockObservation, h, Sum.inl.injEq] at hclock
      cases hclock
      rfl
  | ok started => simp only [clockObservation, h, Sum.inr_ne_inl] at hclock

/-- Recover the equation of the retained original successful clock result. -/
theorem clockObservation_ok (z : LocalInput p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hclock : clockObservation z = .inr started) :
    CoordinatorPhaseClock.startRound p rate.eta.val (assemble z).time
      (assemble z).clock (assemble z).ledger.pending = .ok started := by
  cases h : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z).time
      (assemble z).clock (assemble z).ledger.pending with
  | error reason => simp only [clockObservation, h, Sum.inl_ne_inr] at hclock
  | ok result =>
      simp only [clockObservation, h, Sum.inr.injEq] at hclock
      cases hclock
      rfl

def restoreClockData (z : CoreInput p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z.val).time
      (assemble z.val).clock (assemble z.val).ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hi : started.assignmentStart = some instruction)
    (output : LaterAssignmentStartOperation.SuccessfulStart z.val.1.1
      (operationLedger z) instruction z.val.1.2)
    (hlocal : output.localConsistency = localConsistency z) :
    CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := by
  have ht := (CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val
    (assemble z.val).time (assemble z.val).clock (assemble z.val).ledger.pending
    started instruction z.property.clock_parameter_valid z.property.clock_registers_valid
    z.property.clock_start_time_valid hstart hi).1
  exact {
    priorClock := (assemble z.val).clock
    pending := (assemble z.val).ledger.pending
    proposalParameterValid := z.property.clock_parameter_valid
    priorClockValid := z.property.clock_registers_valid
    startTimeValid := by rw [ht]; exact z.property.clock_start_time_valid
    result := started
    startRound_eq := by rw [ht]; exact hstart
    assignmentStart_eq := hi
    priorSigma_eq := z.property.clock_sigma_eq
    priorGrid_eq_freezeAt := by
      rw [hlocal]
      exact z.property.ledger_freeze_eq.symm }

/-- Restore the installed registers from the retained coordinates. The
supplied result equation is a local decoder certificate, not a public input
to the unrestricted joint theorem. -/
def rebuildLaterOutcome (z : CoreInput p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z.val).time
      (assemble z.val).clock (assemble z.val).ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hi : started.assignmentStart = some instruction)
    (result : LaterAssignmentStartOperation.Result z.val.1.1 (operationLedger z)
      instruction z.val.1.2 (localConsistency z))
    (hr : LaterAssignmentStartOperation.laterAssignmentStart z.val.1.1 (operationLedger z)
      instruction z.val.1.2 (localConsistency z) = result)
    (installed : Option (InstalledObservation p rate)) (tag : CollectionTag p) :
    Option (CoordinatorRoundDispatch.CollectionOutcome (assemble z.val)) := by
  classical
  match result with
  | .reconstructionFailure reason =>
      exact some (.laterReconstructionFailure z.property (localConsistency z)
        started hstart instruction hi reason hr)
  | .prefixFailure arm reason =>
      exact some (.laterPrefixFailure z.property (localConsistency z)
        started hstart instruction hi arm reason hr)
  | .orientationFailure set =>
      exact some (.laterOrientationFailure z.property (localConsistency z)
        started hstart instruction hi set hr)
  | .success output hlocal =>
      let clockData := restoreClockData z started hstart instruction hi output hlocal
      match installed with
      | none => exact none
      | some c =>
          let installation := restoreInstallation z instruction output clockData c.1
          match tag with
          | .laterChoiceFailure reason =>
              exact some (.laterChoiceFailure z.property (localConsistency z)
                started hstart instruction hi output hlocal clockData installation reason)
          | .laterChosen =>
              match c.2.2.2.2.2.2.2 with
              | none => exact none
              | some arm =>
                  if hv : CoordinatorLocalArmChoice.ChoiceInputsValid
                      installation.registers.payload
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                      instruction.time installation.registers.complementWeights then
                    if hs : CoordinatorLocalArmChoice.coordinatorArmChoice
                        installation.registers.payload started.pending
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                        instruction.time installation.registers.complementWeights z.val.1.2 =
                          some arm then
                      exact some (.laterChosen z.property (localConsistency z)
                        started hstart instruction hi output hlocal clockData installation {
                          arm := arm, choiceInputsValid := hv
                          recorderBoundaryValid :=
                            CoordinatorPhaseClock.startRoundResult_grid_upper_bound p started
                          armChoice_eq := hs })
                    else exact none
                  else exact none
          | _ => exact none

/-- Restore the literal payload fields; the tests supply domain certificates. -/
def restorePayload (v : LaterAssignmentStartMeasurability.PayloadObservation p) :
    Option (Payload rate) := by
  classical
  exact if h : (v.1 : ℝ) = rate.eta.val * (D p : ℝ) ∧
      v.2.2.1 ∈ ProductSetLaw.support p.K (p.m - 1) ∧
      (∀ a, 0 < v.2.2.2.1 a) ∧ (∀ a, v.2.2.2.2 a ≤ p.T * D p) then
    some {
      eta_le_source_cap := rate.sourceCap
      n := v.1
      n_eq_eta_mul_D := h.1
      sigma := v.2.1
      slowSet := ⟨v.2.2.1, h.2.1⟩
      anchor := v.2.2.2.1
      anchor_pos := h.2.2.1
      queues := v.2.2.2.2
      queues_le_TD := h.2.2.2 }
    else none

theorem restorePayload_exact (payload : Payload rate) :
    restorePayload (LaterAssignmentStartMeasurability.payloadObservation payload) =
      some payload := by
  unfold restorePayload
  split
  · rfl
  · rename_i h
    exact False.elim (h ⟨payload.n_eq_eta_mul_D, payload.slowSet.property,
      payload.anchor_pos, payload.queues_le_TD⟩)

/-- Restore complete registers from retained options. No missing coordinate
is replaced by a default. Original inputs occur only in certificate tests. -/
def restoreReconstruction (z : CoreInput p rate)
    (i : CoordinatorPhaseClock.AssignmentStartInstruction p) (r : RegisterObservation p) :
    Option (AssignmentScoreReconstruction.ReconstructedStart (operationLedger z) i) := by
  classical
  if hpresent : (∀ a, (r.1 a).isSome) ∧ (∀ a, (r.2 a).isSome) then
    let cutoff (a : Fin p.K) : CoordinatorCollectionLedger.CutoffRegister :=
      let q := (r.1 a).get (hpresent.1 a)
      ⟨q.1, q.2.1, q.2.2⟩
    let current (a : Fin p.K) : CoordinatorCollectionLedger.CurrentRegister :=
      let q := (r.2 a).get (hpresent.2 a)
      ⟨q.1, q.2⟩
    exact if h : (∀ a, (operationLedger z).cutoffRegisters a = some (cutoff a)) ∧
        (∀ a, (operationLedger z).currentRegisters a = some (current a)) ∧
        (∀ a, (cutoff a).score + (operationLedger z).increment a ≤ p.T * D p) ∧
        (∀ a, (current a).queue ≤ p.T * D p) ∧
        (∀ a, i.time.val + 1 < (operationLedger z).freezeAt →
          (cutoff a).lastService ≤ (cutoff a).score) ∧
        (∀ a, i.time.val + 1 < (operationLedger z).freezeAt →
          (cutoff a).score - (cutoff a).lastService ≤ p.T * D p) then
      some {
        registers := ⟨cutoff, current, h.1, h.2.1⟩
        currentScore_le := h.2.2.1
        initialQueue_le := h.2.2.2.1
        previousScore_nonnegative := h.2.2.2.2.1
        previousScore_le := h.2.2.2.2.2 }
      else none
  else exact none

theorem restoreReconstruction_exact (z : CoreInput p rate)
    (i : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart (operationLedger z) i) :
    restoreReconstruction z i (registerObservation z.val) = some out := by
  have he : registerObservation z.val =
      ((fun a => some ((out.registers.cutoff a).score,
        (out.registers.cutoff a).queue, (out.registers.cutoff a).lastService)),
        fun a => some ((out.registers.current a).queue,
          (out.registers.current a).lastService)) := by
    apply Prod.ext <;> funext a
    · change ((operationLedger z).cutoffRegisters a).map _ = _
      rw [out.registers.cutoff_eq a]; rfl
    · change ((operationLedger z).currentRegisters a).map _ = _
      rw [out.registers.current_eq a]; rfl
  rw [he]
  unfold restoreReconstruction
  simp only [Option.isSome_some, implies_true, and_self, dite_true, Option.get_some]
  split
  · rfl
  · rename_i h
    exact False.elim (h ⟨out.registers.cutoff_eq, out.registers.current_eq,
      out.currentScore_le, out.initialQueue_le, out.previousScore_nonnegative, out.previousScore_le⟩)

/-- Every data field below comes from the stored full later observation.
The noncomputable proposition tests supply only dependent certificates. -/
def restoreSampledResult (z : CoreInput p rate)
    (i : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart (operationLedger z) i)
    (parameters : CheckedAssignmentJointMeasurability.RawMass p ×
      CheckedAssignmentJointMeasurability.Anchor p)
    (sample : OrientedAssignmentLaw.AssignmentOutcome p.K p.m)
    (vector : CheckedAssignmentSample.AssignmentVector p) (payload : Payload rate)
    (scores : Fin (p.m - 1) → ℕ)
    (derived : LaterAssignmentFullOutputMeasurability.DerivedOutputFields p) :
    Option (LaterAssignmentStartOperation.Result z.val.1.1 (operationLedger z) i
      z.val.1.2 (localConsistency z)) := by
  classical
  if hpos : ∀ a, 0 < parameters.2 a then
    let law : LaterAssignmentStartOperation.SelectedLaw z.val.1.1 (operationLedger z) i out :=
      ⟨parameters.1, parameters.2, hpos⟩
    if h : AssignmentScoreReconstruction.reconstructLaterStart (operationLedger z) i =
          .success (operationLedger z) i out ∧
        (operationLedger z).cutoff ≤ i.time.val + 1 ∧
        (∀ a, 0 < AssignmentScoreReconstruction.currentWeight out a) ∧
        (∀ a, 0 < AssignmentScoreReconstruction.cutoffWeight out a) then
      exact if hc : LaterAssignmentStartOperation.selectLaw? z.val.1.1 (operationLedger z) i
            out h.2.1 h.2.2.1 = some law ∧
          payload.slowSet = CheckedAssignmentOrientation.slowSetAfter p
            sample.1.1 sample.1.2 sample.2 ∧
          vector = LaterAssignmentStartOperation.ownAssignmentVector z.val.1.2 i.time ∧
          CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor vector =
            .sampled sample ∧
          payload = LaterAssignmentStartOperation.payloadInput z.val.1.1 i out law payload.slowSet ∧
          (∀ a, scores a = AssignmentScoreReconstruction.sourceScore out
            (payload.assignment.assigned a)) ∧
          derived = AssignmentPayloadDerivedMeasurability.inputDerivedFields payload then
        some (.success {
          localConsistency := localConsistency z, reconstruction := out, reconstruction_eq := h.1,
          cutoffReached := h.2.1, currentWeight_pos := h.2.2.1, cutoffWeight_pos := h.2.2.2,
          law := law, law_selected := hc.1, outcome := sample, slowSet := payload.slowSet,
          slowSet_eq_erasure := hc.2.1, assignmentVector := vector,
          assignmentVector_eq_row_projection := hc.2.2.1, checkedSample_eq := hc.2.2.2.1,
          payload := payload, payload_eq_input := hc.2.2.2.2.1,
          payload_start := by rw [hc.2.2.2.2.1]; rfl,
          payload_anchor := by rw [hc.2.2.2.2.1]; rfl,
          payload_slowSet := rfl,
          payload_queues := by intro a; rw [hc.2.2.2.2.1]; rfl,
          baseScore := scores, baseScore_eq_source := hc.2.2.2.2.2.1 } rfl)
        else none
    else exact none
  else exact none

def retainedResult (z : CoreInput p rate)
    (i : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (later : LaterAssignmentFullOutputMeasurability.FullOutputObservation p)
    (registers : RegisterObservation p) :
    Option (LaterAssignmentStartOperation.Result z.val.1.1 (operationLedger z) i
      z.val.1.2 (localConsistency z)) :=
  match later.1 with
  | .reconstructionFailure reason => some (.reconstructionFailure reason)
  | .prefixFailure arm reason => some (.prefixFailure arm reason)
  | .orientationFailure set => some (.orientationFailure set)
  | .sampled sample => do
      let parameters ← later.2.1
      let payloadScore ← later.2.2.1
      let payload ← restorePayload payloadScore.1
      let derived ← later.2.2.2.2
      let out ← restoreReconstruction z i registers
      restoreSampledResult z i out parameters sample later.2.2.2.1 payload payloadScore.2 derived

theorem selected_parameters_of_success (old : Payload rate)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (i : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger i row) :
    LaterAssignmentStartMeasurability.selectedSamplerParameters? old ⟨ledger, i, consistent⟩ =
      some (output.law.mass, output.law.anchor) := by
  let call : LaterAssignmentStartOperation.ReconstructionCall old ledger i :=
    ⟨.success ledger i output.reconstruction, output.reconstruction_eq⟩
  have he : (⟨AssignmentScoreReconstruction.reconstructLaterStart ledger i, rfl⟩ :
      LaterAssignmentStartOperation.ReconstructionCall old ledger i) = call := by
    apply LaterAssignmentStartOperation.ReconstructionCall.ext
    exact output.reconstruction_eq
  have hd : LaterAssignmentStartOperation.decideReconstruction old ledger i =
      .success output.reconstruction output.reconstruction_eq := by
    unfold LaterAssignmentStartOperation.decideReconstruction
    rw [he]; rfl
  rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match]
  simp only [hd]
  let s := LaterAssignmentStartMeasurability.successfulLawSelection old
    ledger i output.reconstruction output.reconstruction_eq
  have hl : s.law = output.law := Option.some.inj (s.lawSelected.symm.trans output.law_selected)
  change some (s.law.mass, s.law.anchor) = _
  rw [hl]

theorem retainedResult_exact (z : CoreInput p rate)
    (i : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (result : LaterAssignmentStartOperation.Result z.val.1.1 (operationLedger z) i
      z.val.1.2 (localConsistency z))
    (hr : LaterAssignmentStartOperation.laterAssignmentStart z.val.1.1 (operationLedger z) i
      z.val.1.2 (localConsistency z) = result) :
    retainedResult z i (laterObservation z i) (registerObservation z.val) = some result := by
  have hcode : (laterObservation z i).1 = LaterAssignmentStartMeasurability.codeOfResult p result :=
    congrArg (LaterAssignmentStartMeasurability.codeOfResult p) hr
  cases result with
  | reconstructionFailure reason => simp only [retainedResult, hcode,
      LaterAssignmentStartMeasurability.codeOfResult]
  | prefixFailure arm reason => simp only [retainedResult, hcode,
      LaterAssignmentStartMeasurability.codeOfResult]
  | orientationFailure set => simp only [retainedResult, hcode,
      LaterAssignmentStartMeasurability.codeOfResult]
  | success output hlocal =>
      have hparams : (laterObservation z i).2.1 = some (output.law.mass, output.law.anchor) :=
        selected_parameters_of_success z.val.1.1 (operationLedger z) i z.val.1.2
          (localConsistency z) output
      have hp := LaterAssignmentFullOutputMeasurability.fullOutput_success_payloadScore
        (laterInput z i, z.val.1.2) output hlocal hr
      have hd := LaterAssignmentFullOutputMeasurability.fullOutput_success_derivedFields
        (laterInput z i, z.val.1.2) output hlocal hr
      change (laterObservation z i).2.2.1 = some
        (LaterAssignmentStartMeasurability.payloadObservation output.payload, output.baseScore) at hp
      change (laterObservation z i).2.2.2.2 = some
        (AssignmentPayloadDerivedMeasurability.inputDerivedFields output.payload) at hd
      have hv : (laterObservation z i).2.2.2.1 = output.assignmentVector :=
        output.assignmentVector_eq_row_projection.symm
      simp only [retainedResult, hcode, LaterAssignmentStartMeasurability.codeOfResult,
        hparams, hp, hd, hv,
        restoreReconstruction_exact z i output.reconstruction]
      dsimp only [Bind.bind, Option.bind]
      rw [restorePayload_exact]
      dsimp only [Option.bind]
      unfold restoreSampledResult
      rw [dite_eq_left output.law.anchor_pos]
      dsimp only
      split
      next h =>
        have hslow := output.payload_slowSet
        have hpay : output.payload = LaterAssignmentStartOperation.payloadInput z.val.1.1 i
            output.reconstruction output.law output.payload.slowSet := by
          rw [hslow]; exact output.payload_eq_input
        split
        next hc =>
          cases output
          simp only at hlocal hslow
          cases hlocal
          cases hslow
          rfl
        next hc => exact False.elim (hc ⟨output.law_selected,
          hslow.trans output.slowSet_eq_erasure, output.assignmentVector_eq_row_projection,
          output.checkedSample_eq, hpay, output.baseScore_eq_source, rfl⟩)
      next h => exact False.elim (h ⟨output.reconstruction_eq, output.cutoffReached,
        output.currentWeight_pos, output.cutoffWeight_pos⟩)

/-- Numerical reconstruction is a literal restoration from retained data.
The final equality test supplies only the outcome constructor's proof field;
no operation result is matched or projected to obtain numerical data. -/
def decodeLaterOutcome (z : CoreInput p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z.val).time
      (assemble z.val).clock (assemble z.val).ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hi : started.assignmentStart = some instruction)
    (later : LaterAssignmentFullOutputMeasurability.FullOutputObservation p)
    (registers : RegisterObservation p)
    (installed : Option (InstalledObservation p rate)) (tag : CollectionTag p) :
    Option (CoordinatorRoundDispatch.CollectionOutcome (assemble z.val)) := by
  classical
  match retainedResult z instruction later registers with
  | none => exact none
  | some result =>
      exact if hr : LaterAssignmentStartOperation.laterAssignmentStart z.val.1.1
          (operationLedger z) instruction z.val.1.2 (localConsistency z) = result then
        rebuildLaterOutcome z started hstart instruction hi result hr installed tag
      else none

/-- Conditional decoder identity, discharged from actual dispatch in the joint theorem. -/
theorem decodeLaterOutcome_eq_rebuild (z : CoreInput p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z.val).time
      (assemble z.val).clock (assemble z.val).ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hi : started.assignmentStart = some instruction)
    (result : LaterAssignmentStartOperation.Result z.val.1.1 (operationLedger z)
      instruction z.val.1.2 (localConsistency z))
    (hr : LaterAssignmentStartOperation.laterAssignmentStart z.val.1.1 (operationLedger z)
      instruction z.val.1.2 (localConsistency z) = result)
    (installed : Option (InstalledObservation p rate)) (tag : CollectionTag p) :
    decodeLaterOutcome z started hstart instruction hi (laterObservation z instruction)
        (registerObservation z.val) installed tag =
      rebuildLaterOutcome z started hstart instruction hi result hr installed tag := by
  simp only [decodeLaterOutcome, retainedResult_exact z instruction result hr, dite_eq_left hr]

/-- Same-input whole-outcome decoder. Its only certificate argument identifies
the retained clock observation with the original one. Domain and arm equations
are checked to restore proof fields. Later numerical fields are restored from
the retained observations; operation calls supply no numerical decoder data. -/
def decodeCollectionFullObservation (z : LocalInput p rate) (obs : FullObservation p rate)
    (hclock : obs.1.1.1 = clockObservation z) :
    Option (CoordinatorRoundDispatch.CollectionOutcome (assemble z)) := by
  classical
  match hobs : obs.1.1.1 with
  | .inl failure =>
      exact some (.clockFailure failure
        (clockObservation_error z failure (hclock.symm.trans hobs)))
  | .inr started =>
      have hevidence := clockObservation_ok z started (hclock.symm.trans hobs)
      if hcore : CoordinatorRoundDispatch.CollectionCoreValid (assemble z) then
        let core : CoreInput p rate := ⟨z, hcore⟩
        match obs.2.2.1 with
        | .coreFailure reason => exact some (.coreFailure hcore started hevidence reason)
        | .continuing =>
            if hpending : z.2.1.pending.Nonempty then
              if hscores : CoordinatorRoundDispatch.collectionCurrentScoresCheck (assemble z) = true then
                match obs.1.2 with
                | none => exact none
                | some c => match c.2.2 with
                  | none => exact none
                  | some arm =>
                      if hv : CoordinatorLocalArmChoice.ChoiceInputsValid (assemble z).payload
                          (some (CoordinatorCollectionUpRoundStep.localCutoff (assemble z).cutoffIndex))
                          (assemble z).time (CoordinatorCollectionInteractive.PreObservationInputs.weights
                            (assemble z) hcore.ledger_valid hcore.assignment_eq) then
                        if hs : CoordinatorLocalArmChoice.coordinatorArmChoice (assemble z).payload
                            started.pending
                            (some (CoordinatorCollectionUpRoundStep.localCutoff (assemble z).cutoffIndex))
                            (assemble z).time (CoordinatorCollectionInteractive.PreObservationInputs.weights
                              (assemble z) hcore.ledger_valid hcore.assignment_eq)
                            (assemble z).row = some arm then
                          exact some (.continuing hcore
                            (restorePrepared core hpending started hevidence arm hv hs)
                            (CoordinatorPhaseClock.startRoundResult_grid_upper_bound p started) hscores)
                        else exact none
                      else exact none
              else exact none
            else exact none
        | .laterFailure _ | .laterChoiceFailure _ | .laterChosen =>
            match hi : started.assignmentStart with
            | none => exact none
            | some instruction =>
                match obs.1.1.2.2.2.2 with
                | none => exact none
                | some later =>
                    exact decodeLaterOutcome core started hevidence instruction hi
                      later obs.2.2.2.2 obs.2.1 obs.2.2.1
        | _ => exact none
      else
        match obs.2.2.1 with
        | .localFailure reason => exact some (.localFailure started hevidence hcore reason)
        | _ => exact none

/-- Literal branch selector used only by the decoder's equational API. -/
def isLaterTag : CollectionTag p → Prop
  | .laterFailure _ | .laterChoiceFailure _ | .laterChosen => True
  | _ => False

theorem decodeFull_later_eq (z : CoreInput p rate) (obs : FullObservation p rate)
    (hclock : obs.1.1.1 = clockObservation z.val)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z.val).time
      (assemble z.val).clock (assemble z.val).ledger.pending = .ok started)
    (hc : obs.1.1.1 = .inr started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hi : started.assignmentStart = some instruction)
    (later : LaterAssignmentFullOutputMeasurability.FullOutputObservation p)
    (hlater : obs.1.1.2.2.2.2 = some later)
    (tag : CollectionTag p) (ht : obs.2.2.1 = tag) (hbranch : isLaterTag tag) :
    decodeCollectionFullObservation z.val obs hclock =
      decodeLaterOutcome z started hstart instruction hi later obs.2.2.2.2 obs.2.1 tag := by
  classical
  unfold decodeCollectionFullObservation
  split
  next failure he =>
    have h : Sum.inl failure = (Sum.inr started : ClockObservation p) := he.symm.trans hc
    cases h
  next got he =>
    have h : got = started := Sum.inr.inj (he.symm.trans hc)
    subst got
    split
    next hcore =>
      cases tag <;> simp only [isLaterTag] at hbranch
      all_goals
        simp only [ht]
        split
        next hn =>
          have h : (none : Option (CoordinatorPhaseClock.AssignmentStartInstruction p)) =
              some instruction := hn.symm.trans hi
          cases h
        next gotInstruction he =>
          have h : gotInstruction = instruction := Option.some.inj (he.symm.trans hi)
          subst gotInstruction
          simp only [hlater]
    next hcore => exact False.elim (hcore z.property)

theorem rebuildLaterOutcome_chosen (z : CoreInput p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z.val).time
      (assemble z.val).clock (assemble z.val).ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hi : started.assignmentStart = some instruction)
    (output : LaterAssignmentStartOperation.SuccessfulStart z.val.1.1
      (operationLedger z) instruction z.val.1.2)
    (hlocal : output.localConsistency = localConsistency z)
    (hr : LaterAssignmentStartOperation.laterAssignmentStart z.val.1.1 (operationLedger z)
      instruction z.val.1.2 (localConsistency z) = .success output hlocal)
    (c : InstalledObservation p rate)
    (selected : CoordinatorRoundDispatch.ArmSelection
      (restoreInstallation z instruction output
        (restoreClockData z started hstart instruction hi output hlocal) c.1).registers.payload
      started instruction.time (restoreInstallation z instruction output
        (restoreClockData z started hstart instruction hi output hlocal) c.1).registers.complementWeights z.val.1.2)
    (hc : c.2.2.2.2.2.2.2 = some selected.arm) :
    rebuildLaterOutcome z started hstart instruction hi (.success output hlocal) hr
      (some c) .laterChosen =
      some (.laterChosen z.property (localConsistency z) started hstart instruction hi output
        hlocal (restoreClockData z started hstart instruction hi output hlocal)
        (restoreInstallation z instruction output
          (restoreClockData z started hstart instruction hi output hlocal) c.1) selected) := by
  classical
  unfold rebuildLaterOutcome
  simp only [hc]
  split
  next hv =>
    split
    next hs => cases selected; rfl
    next hs => exact False.elim (hs selected.armChoice_eq)
  next hv => exact False.elim (hv selected.choiceInputsValid)

theorem decodeFull_clock_eq (z : LocalInput p rate) (obs : FullObservation p rate)
    (hclock : obs.1.1.1 = clockObservation z) (failure : CoordinatorPhaseClock.ClockFailure)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z).time
      (assemble z).clock (assemble z).ledger.pending = .error failure)
    (hc : obs.1.1.1 = .inl failure) :
    decodeCollectionFullObservation z obs hclock = some (.clockFailure failure hstart) := by
  unfold decodeCollectionFullObservation
  split
  next got he =>
    have h : got = failure := Sum.inl.inj (he.symm.trans hc)
    subst got
    rfl
  next got he => cases he.symm.trans hc

theorem decodeFull_core_eq (z : CoreInput p rate) (obs : FullObservation p rate)
    (hclock : obs.1.1.1 = clockObservation z.val)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z.val).time
      (assemble z.val).clock (assemble z.val).ledger.pending = .ok started)
    (hc : obs.1.1.1 = .inr started) (reason : CoordinatorRoundDispatch.CollectionFailure)
    (ht : obs.2.2.1 = .coreFailure reason) :
    decodeCollectionFullObservation z.val obs hclock =
      some (.coreFailure z.property started hstart reason) := by
  classical
  unfold decodeCollectionFullObservation
  split
  next got he => cases he.symm.trans hc
  next got he =>
    have h : got = started := Sum.inr.inj (he.symm.trans hc)
    subst got
    split
    next _ => simp only [ht]
    next hn => exact False.elim (hn z.property)

theorem decodeFull_local_eq (z : LocalInput p rate) (obs : FullObservation p rate)
    (hclock : obs.1.1.1 = clockObservation z)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z).time
      (assemble z).clock (assemble z).ledger.pending = .ok started)
    (hc : obs.1.1.1 = .inr started) (reason : CoordinatorRoundDispatch.CollectionFailure)
    (ht : obs.2.2.1 = .localFailure reason)
    (hcore : ¬CoordinatorRoundDispatch.CollectionCoreValid (assemble z)) :
    decodeCollectionFullObservation z obs hclock =
      some (.localFailure started hstart hcore reason) := by
  classical
  unfold decodeCollectionFullObservation
  split
  next got he => cases he.symm.trans hc
  next got he =>
    have h : got = started := Sum.inr.inj (he.symm.trans hc)
    subst got
    split
    next hv => exact False.elim (hcore hv)
    next _ => simp only [ht]

theorem decodeFull_continuing_eq (z : CoreInput p rate) (obs : FullObservation p rate)
    (hclock : obs.1.1.1 = clockObservation z.val)
    (prepared : CoordinatorCollectionInteractive.PreparedSnapshot (assemble z.val))
    (hscores : CoordinatorRoundDispatch.collectionCurrentScoresCheck (assemble z.val) = true)
    (hc : obs.1.1.1 = .inr prepared.clockStarted) (ht : obs.2.2.1 = .continuing)
    (c : ContinuingObservation p rate) (hcont : obs.1.2 = some c)
    (hchosen : c.2.2 = some prepared.arm) :
    decodeCollectionFullObservation z.val obs hclock =
      some (.continuing z.property prepared
        (CoordinatorPhaseClock.startRoundResult_grid_upper_bound p prepared.clockStarted) hscores) := by
  classical
  unfold decodeCollectionFullObservation
  split
  next got he => cases he.symm.trans hc
  next got he =>
    have h : got = prepared.clockStarted := Sum.inr.inj (he.symm.trans hc)
    subst got
    split
    next _ =>
      have hp : z.val.2.1.pending.Nonempty := prepared.inputsValid.pending_nonempty
      simp only [ht, dite_eq_left hp, dite_eq_left hscores, hcont, hchosen]
      split
      next hv =>
        split
        next hs => cases prepared; rfl
        next hs => exact False.elim (hs prepared.armChoice_eq)
      next hv => exact False.elim (hv prepared.inputsValid.choice_valid)
    next hn => exact False.elim (hn z.property)

/-- Literal selection coordinates of every original local outcome. -/
def outcomeSelectionCode (z : LocalInput p rate) :
    CoordinatorRoundDispatch.CollectionOutcome (assemble z) → Option (SelectionCoordinates p rate)
  | .continuing core prepared _ _ =>
      some (continuingView ⟨z, core⟩ prepared.clockStarted, prepared.clockStarted, prepared.arm)
  | .laterChosen _ _ started _ _ _ _ _ _ installed selected =>
      some (({ payload := installed.registers.payload
               pendingAtChoice := started.pending
               cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
               complementWeights := installed.registers.complementWeights } :
        ReferenceDownReception.ChoiceTimeView p rate.eta), started, selected.arm)
  | _ => none

/-- Unrestricted joint exactness, by analysis of the literal dispatch call. -/
theorem collectionFullObservation_exact (z : LocalInput p rate) :
    collectionTag z = outcomeTag (CoordinatorRoundDispatch.dispatchCollection (assemble z)) ∧
      decodeCollectionFullObservation z (collectionFullObservation z) rfl =
        some (CoordinatorRoundDispatch.dispatchCollection (assemble z)) ∧
      collectionSelectionCode z =
        outcomeSelectionCode z (CoordinatorRoundDispatch.dispatchCollection (assemble z)) := by
  classical
  generalize hout : CoordinatorRoundDispatch.dispatchCollection (assemble z) = outcome
  unfold CoordinatorRoundDispatch.dispatchCollection at hout
  split at hout
  next failure hstart =>
      have hclock : clockObservation z = .inl failure := by
        change (match CoordinatorPhaseClock.startRound p (assemble z).etaReal
          (assemble z).time (assemble z).clock (assemble z).ledger.pending with
          | .error r => Sum.inl r | .ok r => Sum.inr r) = _
        rw [hstart]
      cases hout
      have htag : collectionTag z = .clockFailure := by
        simp only [collectionTag, tagKey, hclock, tagFromKey]
      refine ⟨htag, ?_⟩
      constructor
      · exact decodeFull_clock_eq z (collectionFullObservation z) rfl failure hstart hclock
      · simp [collectionSelectionCode, htag, outcomeSelectionCode]
  next started hstart =>
      have hclock : clockObservation z = .inr started := by
        change (match CoordinatorPhaseClock.startRound p (assemble z).etaReal
          (assemble z).time (assemble z).clock (assemble z).ledger.pending with
          | .error r => Sum.inl r | .ok r => Sum.inr r) = _
        rw [hstart]
      by_cases hcore : CoordinatorRoundDispatch.CollectionCoreValid (assemble z)
      · simp only [dite_eq_left hcore] at hout
        by_cases hpending : (assemble z).ledger.pending.Nonempty
        · simp only [dite_eq_left hpending] at hout
          have heq : started = carriedStart ⟨⟨z, hcore⟩, hpending⟩ :=
            Except.ok.inj (hstart.symm.trans (carriedStart_eq_actual ⟨⟨z, hcore⟩, hpending⟩))
          subst started
          by_cases hscores : CoordinatorRoundDispatch.collectionCurrentScoresCheck (assemble z) = true
          · simp only [dite_eq_left hscores] at hout
            have hcont := continuingObservation?_eq z hcore hpending hscores
            by_cases hv : CoordinatorLocalArmChoice.ChoiceInputsValid (assemble z).payload
                (some (CoordinatorCollectionUpRoundStep.localCutoff (assemble z).cutoffIndex))
                (assemble z).time (CoordinatorCollectionInteractive.PreObservationInputs.weights
                  (assemble z) hcore.ledger_valid hcore.assignment_eq)
            · simp only [dite_eq_left hv] at hout
              split at hout
              next ha =>
                  exact False.elim
                    ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none _ _ _ _ _ _ hv) ha)
              next arm ha =>
                  change (continuingObservation ⟨⟨z, hcore⟩, hpending⟩).2.2 = some arm at ha
                  cases hout
                  have htag : collectionTag z = .continuing := by
                    simp only [collectionTag, tagKey, hclock, coreCheck,
                      ite_eq_left hcore, decide_eq_true hpending, hscores, hcont,
                      Option.map_some, ha, tagFromKey, ite_true]
                  refine ⟨htag, ?_⟩
                  constructor
                  · apply decodeFull_continuing_eq ⟨z, hcore⟩ (collectionFullObservation z) rfl
                      (hscores := hscores) (c := continuingObservation ⟨⟨z, hcore⟩, hpending⟩)
                    · exact hclock
                    · exact htag
                    · exact hcont
                    · exact ha
                  · have hdata : continuingObservation ⟨⟨z, hcore⟩, hpending⟩ =
                        (continuingView ⟨z, hcore⟩ (carriedStart ⟨⟨z, hcore⟩, hpending⟩),
                          carriedStart ⟨⟨z, hcore⟩, hpending⟩, some arm) := Prod.ext rfl (Prod.ext rfl ha)
                    simp only [collectionSelectionCode, htag, hcont, hdata, optionalElim,
                      selectionFromCandidate, Option.map_some, ite_true, outcomeSelectionCode]
            · simp only [dite_eq_right hv] at hout
              have hn : (continuingObservation ⟨⟨z, hcore⟩, hpending⟩).2.2 = none := by
                have hv' : ¬ CoordinatorLocalArmChoice.ChoiceInputsValid
                    (continuingView ⟨z, hcore⟩ (carriedStart ⟨⟨z, hcore⟩, hpending⟩)).payload
                    (continuingView ⟨z, hcore⟩ (carriedStart ⟨⟨z, hcore⟩, hpending⟩)).cutoff
                    (assemble z).time
                    (continuingView ⟨z, hcore⟩ (carriedStart ⟨⟨z, hcore⟩, hpending⟩)).complementWeights := hv
                change CoordinatorLocalArmChoice.coordinatorArmChoice _ _ _ _ _ _ = none
                simp only [CoordinatorLocalArmChoice.coordinatorArmChoice,
                  CoordinatorLocalArmChoice.coordinatorArmChoiceCore, dite_eq_right hv']
              cases hout
              have htag : collectionTag z = .coreFailure .choiceDomainFailure := by
                simp only [collectionTag, tagKey, hclock, coreCheck,
                  ite_eq_left hcore, decide_eq_true hpending, hscores, hcont, Option.map_some,
                  hn, tagFromKey, ite_true]
              refine ⟨htag, ?_⟩
              constructor
              · exact decodeFull_core_eq ⟨z, hcore⟩ (collectionFullObservation z) rfl (carriedStart ⟨⟨z, hcore⟩, hpending⟩) hstart hclock .choiceDomainFailure htag
              · simp [collectionSelectionCode, htag, outcomeSelectionCode]
          · simp only [dite_eq_right hscores] at hout
            cases hout
            have hf := Bool.eq_false_of_not_eq_true hscores
            have htag : collectionTag z = .coreFailure .currentScoreDomainFailure := by
              simp only [collectionTag, tagKey, hclock, coreCheck,
                ite_eq_left hcore, decide_eq_true hpending, hf, tagFromKey, ite_true, ite_false, Bool.false_eq_true]
            refine ⟨htag, ?_⟩
            constructor
            · exact decodeFull_core_eq ⟨z, hcore⟩ (collectionFullObservation z) rfl (carriedStart ⟨⟨z, hcore⟩, hpending⟩) hstart hclock .currentScoreDomainFailure htag
            · simp [collectionSelectionCode, htag, outcomeSelectionCode]
        · simp only [dite_eq_right hpending] at hout
          split at hout
          next hi =>
              cases hout
              have htag : collectionTag z = .coreFailure .assignmentInstructionMissing := by
                simp only [collectionTag, tagKey, hclock, coreCheck,
                  ite_eq_left hcore, decide_eq_false hpending, hi, tagFromKey, ite_true, ite_false, Bool.false_eq_true]
              refine ⟨htag, ?_⟩
              constructor
              · exact decodeFull_core_eq ⟨z, hcore⟩ (collectionFullObservation z) rfl started hstart hclock .assignmentInstructionMissing htag
              · simp [collectionSelectionCode, htag, outcomeSelectionCode]
          next instruction hi =>
              let core : CoreInput p rate := ⟨z, hcore⟩
              have hrequest : requestedInstruction z = some instruction := by
                have hp : ¬z.2.1.pending.Nonempty := hpending
                simp only [requestedInstruction, requestedInstructionAt, ite_eq_right hp, hclock, hi]
              have hfull := laterObservation?_of_instruction z hcore instruction hrequest
              have decodeLater (result : LaterAssignmentStartOperation.Result core.val.1.1
                  (operationLedger core) instruction core.val.1.2 (localConsistency core))
                  (hr : LaterAssignmentStartOperation.laterAssignmentStart core.val.1.1
                    (operationLedger core) instruction core.val.1.2 (localConsistency core) = result)
                  (tag : CollectionTag p) (htag : collectionTag z = tag) (hbranch : isLaterTag tag) :
                  decodeCollectionFullObservation z (collectionFullObservation z) rfl =
                    rebuildLaterOutcome core started hstart instruction hi result hr
                      (collectionFullObservation z).2.1 tag :=
                (decodeFull_later_eq core (collectionFullObservation z) rfl started hstart
                  hclock instruction hi (laterObservation core instruction) hfull tag htag hbranch).trans
                  (decodeLaterOutcome_eq_rebuild core started hstart instruction hi result hr
                    (collectionFullObservation z).2.1 tag)
              have hcode := later_code_observed core started hstart hpending instruction hi
              split at hout
              next reason hr =>
                  change LaterAssignmentStartOperation.laterAssignmentStart core.val.1.1
                    (operationLedger core) instruction core.val.1.2
                    (localConsistency core) = _ at hr
                  rw [hr] at hcode
                  dsimp only [core] at hcode
                  cases hout
                  have htag : collectionTag z = .laterFailure (.reconstructionFailure reason) := by
                    simp only [collectionTag, tagKey, hclock, coreCheck,
                      ite_eq_left hcore, decide_eq_false hpending, hi, hcode,
                      LaterAssignmentStartMeasurability.codeOfResult, tagFromKey, ite_true, ite_false, Bool.false_eq_true]
                  refine ⟨htag, ?_⟩
                  constructor
                  · have hdecoded := decodeLater (.reconstructionFailure reason) hr
                      (.laterFailure (.reconstructionFailure reason)) htag (by trivial)
                    exact hdecoded.trans (by rfl)
                  · simp [collectionSelectionCode, htag, outcomeSelectionCode]
              next arm reason hr =>
                  change LaterAssignmentStartOperation.laterAssignmentStart core.val.1.1
                    (operationLedger core) instruction core.val.1.2
                    (localConsistency core) = _ at hr
                  rw [hr] at hcode
                  dsimp only [core] at hcode
                  cases hout
                  have htag : collectionTag z = .laterFailure (.prefixFailure arm reason) := by
                    simp only [collectionTag, tagKey, hclock, coreCheck,
                      ite_eq_left hcore, decide_eq_false hpending, hi, hcode,
                      LaterAssignmentStartMeasurability.codeOfResult, tagFromKey, ite_true, ite_false, Bool.false_eq_true]
                  refine ⟨htag, ?_⟩
                  constructor
                  · have hdecoded := decodeLater (.prefixFailure arm reason) hr
                      (.laterFailure (.prefixFailure arm reason)) htag (by trivial)
                    exact hdecoded.trans (by rfl)
                  · simp [collectionSelectionCode, htag, outcomeSelectionCode]
              next set hr =>
                  change LaterAssignmentStartOperation.laterAssignmentStart core.val.1.1
                    (operationLedger core) instruction core.val.1.2
                    (localConsistency core) = _ at hr
                  rw [hr] at hcode
                  dsimp only [core] at hcode
                  cases hout
                  have htag : collectionTag z = .laterFailure (.orientationFailure set) := by
                    simp only [collectionTag, tagKey, hclock, coreCheck,
                      ite_eq_left hcore, decide_eq_false hpending, hi, hcode,
                      LaterAssignmentStartMeasurability.codeOfResult, tagFromKey, ite_true, ite_false, Bool.false_eq_true]
                  refine ⟨htag, ?_⟩
                  constructor
                  · have hdecoded := decodeLater (.orientationFailure set) hr
                      (.laterFailure (.orientationFailure set)) htag (by trivial)
                    exact hdecoded.trans (by rfl)
                  · simp [collectionSelectionCode, htag, outcomeSelectionCode]
              next output hlocal hr =>
                  change @LaterAssignmentStartOperation.SuccessfulStart p rate.eta core.val.1.1
                    (operationLedger core) instruction core.val.1.2 at output
                  change LaterAssignmentStartOperation.laterAssignmentStart core.val.1.1
                    (operationLedger core) instruction core.val.1.2
                    (localConsistency core) = _ at hr
                  rw [hr] at hcode
                  dsimp only [core] at hcode
                  let clockData := restoreClockData core started hstart instruction hi output hlocal
                  let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
                  have hcresult : clockData.result = started := rfl
                  -- `hr` was obtained by splitting the literal dispatcher computation.
                  -- It is the missing producer equation required by the admitted bridge.
                  have hinst := laterInstalledObservation?_of_actual_success core started
                    hstart hpending instruction hi output hlocal hr
                  have hrestore := restoreInstallation_exact core instruction output clockData
                  have hvview := installedView_eq_actual core instruction output clockData
                  rw [hcresult] at hvview
                  have hpend := pending_new_start core started hstart instruction hi
                  let c := installationCoordinates (output.payload, output.baseScore) z.2.1 instruction started
                  change laterInstalledObservation? z = some (installedObservation c started z.1.2) at hinst
                  change restoreInstallation core instruction output clockData c = installed at hrestore
                  split at hout
                  next hb =>
                    have hbase : installedBaseScoreBit c = true := decide_eq_true hb
                    split at hout
                    next hv =>
                      split at hout
                      next hrec =>
                        split at hout
                        next ha =>
                          exact False.elim
                            ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none _ _ _ _ _ _ hv) ha)
                        next arm ha =>
                          have hchoice : installedChoiceInputsBit c started = true := by
                            unfold installedChoiceInputsBit
                            change ReferenceDownReceptionMeasurability.choiceInputsValidBit
                              (installedView c started) instruction.time = true
                            rw [hvview]
                            exact decide_eq_true hv
                          have hgrid : installedGridBoundaryBit started = true :=
                            decide_eq_true (CoordinatorPhaseClock.startRoundResult_grid_upper_bound p started)
                          have henvelope : installedEnvelopeBit c = true := by
                            have henv : ∀ j : CanonicalFastSampling.FastArm
                                (installedView c started).payload.slowSet,
                                (installedView c started).payload.anchor j.1 ≤
                                    (installedView c started).complementWeights j ∧
                                  (installedView c started).complementWeights j ≤
                                    2 * (installedView c started).payload.anchor j.1 := by
                              rw [hvview]
                              exact fun j => ⟨hv.anchor_le_current j, hv.current_le_twice_anchor j⟩
                            unfold installedEnvelopeBit
                            apply dite_eq_left
                            exact henv
                          have hcand : (installedObservation c started z.1.2).2.2.2.2.2.2.2 = some arm := by
                            change installedSelectedArm c started z.1.2 = _
                            unfold installedSelectedArm
                            rw [hbase, hchoice, hgrid, henvelope]
                            change pendingChoice (installedView c started, z.1.2, instruction.time) = _
                            rw [hvview]
                            unfold pendingChoice
                            dsimp only
                            split
                            · exact ha
                            · rename_i hn
                              exact False.elim (hn hpend)
                          cases hout
                          have htag : collectionTag z = .laterChosen := by
                            simp only [collectionTag, tagKey, hclock, coreCheck,
                              ite_eq_left hcore, decide_eq_false hpending, hi, hcode,
                              LaterAssignmentStartMeasurability.codeOfResult, hinst, Option.map_some,
                              installedObservation, hbase, hchoice, hgrid, henvelope,
                              show installedSelectedArm c started z.1.2 = some arm from hcand, tagFromKey, ite_true, ite_false, Bool.false_eq_true]
                          refine ⟨htag, ?_⟩
                          constructor
                          · have hdecoded := decodeLater (.success output hlocal) hr
                              (.laterChosen) htag (by trivial)
                            have hic : (collectionFullObservation z).2.1 = some (installedObservation c started z.1.2) := hinst
                            have hstep := congrArg (fun ic => rebuildLaterOutcome core started hstart instruction hi
                              (.success output hlocal) hr ic (.laterChosen)) hic
                            let selected : CoordinatorRoundDispatch.ArmSelection output.payload started instruction.time
                                installed.registers.complementWeights z.1.2 := {
                              arm := arm, choiceInputsValid := hv
                              recorderBoundaryValid := CoordinatorPhaseClock.startRoundResult_grid_upper_bound p started
                              armChoice_eq := ha }
                            have hrst : restoreInstallation core instruction output clockData c = installed := hrestore
                            have hchosen := rebuildLaterOutcome_chosen core started hstart instruction hi output hlocal hr
                              (installedObservation c started z.1.2)
                            dsimp only [installedObservation] at hchosen
                            rw [hrst] at hchosen
                            exact hdecoded.trans (hstep.trans (hchosen selected hcand))
                          · have hdata : installedCandidate (installedObservation c started z.1.2) =
                                (installedView c started, started, some arm) := Prod.ext rfl (Prod.ext rfl hcand)
                            change installedView c started = _ at hvview
                            simp only [collectionSelectionCode, htag, reduceCtorEq, ite_false, ite_true,
                              hinst, optionalElim, hdata, selectionFromCandidate, Option.map_some,
                              outcomeSelectionCode, hvview]
                            rfl
                      next hrec =>
                        exact False.elim (hrec (fun j => ⟨hv.anchor_le_current j, hv.current_le_twice_anchor j⟩))
                    next hv =>
                      have hchoice : installedChoiceInputsBit c started = false := by
                        unfold installedChoiceInputsBit
                        change ReferenceDownReceptionMeasurability.choiceInputsValidBit
                          (installedView c started) instruction.time = false
                        rw [hvview]
                        exact decide_eq_false hv
                      cases hout
                      have htag : collectionTag z = .laterChoiceFailure .choiceDomainFailure := by
                        simp only [collectionTag, tagKey, hclock, coreCheck,
                          ite_eq_left hcore, decide_eq_false hpending, hi, hcode,
                          LaterAssignmentStartMeasurability.codeOfResult, hinst, Option.map_some,
                          installedObservation, hbase, hchoice, tagFromKey, ite_true, ite_false, Bool.false_eq_true]
                      refine ⟨htag, ?_⟩
                      constructor
                      · have hdecoded := decodeLater (.success output hlocal) hr
                          (.laterChoiceFailure .choiceDomainFailure) htag (by trivial)
                        have hic : (collectionFullObservation z).2.1 = some (installedObservation c started z.1.2) := hinst
                        have hstep := congrArg (fun ic => rebuildLaterOutcome core started hstart instruction hi
                          (.success output hlocal) hr ic (.laterChoiceFailure .choiceDomainFailure)) hic
                        exact hdecoded.trans (hstep.trans
                          (by
                          simp only [rebuildLaterOutcome, installedObservation]
                          rw [hrestore]
                          rfl))
                      · simp [collectionSelectionCode, htag, outcomeSelectionCode]
                  next hb =>
                    have hbase : installedBaseScoreBit c = false := decide_eq_false hb
                    cases hout
                    have htag : collectionTag z = .laterChoiceFailure .stateDomainFailure := by
                      simp only [collectionTag, tagKey, hclock, coreCheck,
                        ite_eq_left hcore, decide_eq_false hpending, hi, hcode,
                        LaterAssignmentStartMeasurability.codeOfResult, hinst, Option.map_some,
                        installedObservation, hbase, tagFromKey, ite_true, ite_false, Bool.false_eq_true]
                    refine ⟨htag, ?_⟩
                    constructor
                    · have hdecoded := decodeLater (.success output hlocal) hr
                        (.laterChoiceFailure .stateDomainFailure) htag (by trivial)
                      have hic : (collectionFullObservation z).2.1 = some (installedObservation c started z.1.2) := hinst
                      have hstep := congrArg (fun ic => rebuildLaterOutcome core started hstart instruction hi
                        (.success output hlocal) hr ic (.laterChoiceFailure .stateDomainFailure)) hic
                      exact hdecoded.trans (hstep.trans
                        (by
                        simp only [rebuildLaterOutcome, installedObservation]
                        rw [hrestore]
                        rfl))
                    · simp [collectionSelectionCode, htag, outcomeSelectionCode]
      · simp only [dite_eq_right hcore] at hout
        cases hout
        have htag : collectionTag z = .localFailure .stateDomainFailure := by
          simp only [collectionTag, tagKey, hclock, coreCheck,
            ite_eq_right hcore, tagFromKey, ite_false, Bool.false_eq_true]
        refine ⟨htag, ?_⟩
        constructor
        · exact decodeFull_local_eq z (collectionFullObservation z) rfl started hstart hclock .stateDomainFailure htag hcore
        · simp [collectionSelectionCode, htag, outcomeSelectionCode]

theorem collectionTag_eq_actual (z : LocalInput p rate) :
    collectionTag z = outcomeTag (CoordinatorRoundDispatch.dispatchCollection (assemble z)) :=
  (collectionFullObservation_exact z).1

theorem decode_collectionFullObservation_exact (z : LocalInput p rate) :
    decodeCollectionFullObservation z (collectionFullObservation z) rfl =
      some (CoordinatorRoundDispatch.dispatchCollection (assemble z)) :=
  (collectionFullObservation_exact z).2.1

theorem collectionSelectionCode_eq_actual (z : LocalInput p rate) :
    collectionSelectionCode z =
      outcomeSelectionCode z (CoordinatorRoundDispatch.dispatchCollection (assemble z)) :=
  (collectionFullObservation_exact z).2.2
theorem measurable_collectionFullObservation_comp {X : Type*} [MeasurableSpace X]
    (input : X → LocalInput p rate) (hinput : Measurable input) :
    Measurable (fun x => collectionFullObservation (input x)) :=
  measurable_collectionFullObservation.comp hinput
theorem measurable_collectionFullObservation_separate {X : Type*} [MeasurableSpace X]
    (payload : X → Payload rate) (ledger : X → Ledger rate)
    (proposal : X → Option (Fin p.T × Bool)) (bank : X → CoordinatorUpReception.UpDecoderBank p)
    (row : X → CompletePublicTable.CompleteRow p) (time cutoff : X → Fin p.T)
    (hp : Measurable payload) (hl : Measurable ledger) (hq : Measurable proposal)
    (hb : Measurable bank) (hr : Measurable row) (ht : Measurable time) (hc : Measurable cutoff) :
    Measurable (fun x => collectionFullObservation
      ((payload x, row x), ledger x, proposal x, bank x, time x, cutoff x)) :=
  measurable_collectionFullObservation.comp
    ((hp.prodMk hr).prodMk (hl.prodMk (hq.prodMk (hb.prodMk (ht.prodMk hc)))))

/-- Outer cutoff check, with its distinct invalid-cutoff diagnostic. -/
def boundaryFullObservation (z : BoundaryInput p rate) : Unit ⊕ FullObservation p rate := by
  classical
  exact if hc : cutoffValid z then .inr (collectionFullObservation (boundaryLocal ⟨z, hc⟩))
    else .inl ()
theorem measurable_boundaryFullObservation :
    Measurable (boundaryFullObservation (p := p) (rate := rate)) := by
  classical
  exact Measurable.dite
    (measurable_inr.comp (measurable_collectionFullObservation.comp measurable_boundaryLocal))
    measurable_const measurableSet_cutoffValid
theorem measurable_boundaryFullObservation_comp {X : Type*} [MeasurableSpace X]
    (payload : X → Payload rate) (ledger : X → Ledger rate)
    (proposal : X → Option (Fin p.T × Bool)) (bank : X → CoordinatorUpReception.UpDecoderBank p)
    (row : X → CompletePublicTable.CompleteRow p) (time : X → Fin p.T)
    (hp : Measurable payload) (hl : Measurable ledger) (hq : Measurable proposal)
    (hb : Measurable bank) (hr : Measurable row) (ht : Measurable time) :
    Measurable (fun x => boundaryFullObservation
      ((payload x, row x), ledger x, proposal x, bank x, time x)) :=
  measurable_boundaryFullObservation.comp
    ((hp.prodMk hr).prodMk (hl.prodMk (hq.prodMk (hb.prodMk ht))))

/-- Canonical collection projection, retaining invalid cutoffs and phase absence. -/
def canonicalCollectionFullObservation (x : RoundInput p rate) :
    Option (Unit ⊕ FullObservation p rate) :=
  mapOptional (fun q => boundaryFullObservation (attachBoundary q.1 q.2))
    (collectionCoordinates? (encodeCoordinator x.state.coordinator),
      x.row, x.state.upDecoderBank, x.time)
theorem measurable_canonicalCollectionFullObservation :
    Measurable (canonicalCollectionFullObservation (p := p) (rate := rate)) :=
  (measurable_mapOptional _ (measurable_boundaryFullObservation.comp measurable_attachBoundary)).comp
    ((measurable_collectionCoordinates?.comp
      (measurable_coordinatorCode.comp measurable_state)).prodMk
      (measurable_row.prodMk ((measurable_upDecoderBank.comp measurable_state).prodMk measurable_time)))

theorem canonicalCollectionFullObservation_collection (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal) :
    canonicalCollectionFullObservation x = some (boundaryFullObservation
      ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time)) := by
  simp only [canonicalCollectionFullObservation, hstate, encodeCoordinator,
    collectionCoordinates?, mapOptional, Option.map_some, attachBoundary]

def selectionFromBoundary : Unit ⊕ FullObservation p rate → Option (SelectionCoordinates p rate)
  | .inl _ => none
  | .inr o => o.2.2.2.1
theorem measurable_selectionFromBoundary :
    Measurable (selectionFromBoundary (p := p) (rate := rate)) :=
  measurable_fun_sum measurable_const
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))

def canonicalCollectionSelectionCode (x : RoundInput p rate) : Option (SelectionCoordinates p rate) :=
  optionalElim none selectionFromBoundary (canonicalCollectionFullObservation x)
theorem measurable_canonicalCollectionSelectionCode :
    Measurable (canonicalCollectionSelectionCode (p := p) (rate := rate)) :=
  (measurable_optionalElim _ _ measurable_selectionFromBoundary).comp
    measurable_canonicalCollectionFullObservation

theorem canonicalCollectionSelectionCode_eq_dispatch (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal) :
    canonicalCollectionSelectionCode x = (dispatch x).selection.map encodeSelection := by
  classical
  unfold canonicalCollectionSelectionCode
  rw [canonicalCollectionFullObservation_collection x payload ledger proposal hstate]
  simp only [optionalElim]
  let b : BoundaryInput p rate := ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time)
  by_cases hc : cutoffValid b
  · have hd := dispatch_collection x payload ledger proposal hstate hc
    change selectionFromBoundary (boundaryFullObservation b) = _
    simp only [boundaryFullObservation, dite_eq_left hc, selectionFromBoundary]
    rw [hd]
    let z := boundaryLocal ⟨b, hc⟩
    change collectionSelectionCode z = _
    apply (collectionSelectionCode_eq_actual z).trans
    have hselection (outcome : CoordinatorRoundDispatch.CollectionOutcome (assemble z)) :
        outcomeSelectionCode z outcome =
          (DispatchCut.collection payload ledger (assemble z).clock (assemble z).cutoffIndex
            outcome).selection.map encodeSelection := by
      have h := collection_selection_coordinates x payload ledger (assemble z).clock
        (assemble z).cutoffIndex outcome
      cases outcome <;>
        simpa only [outcomeSelectionCode, continuingView, z, b, boundaryLocal, assemble,
          collectionInput, CoordinatorCollectionInteractive.PreObservationInputs.weights] using h.symm
    exact hselection _
  · have hd := dispatch_collection_invalid x payload ledger proposal hstate hc
    change selectionFromBoundary (boundaryFullObservation b) = _
    simp only [boundaryFullObservation, dite_eq_right hc, selectionFromBoundary, hd.1,
      DispatchCut.selection, Option.map_none]

/-- Restore the canonical Selection and its arm-choice certificates. -/
theorem canonicalCollectionSelection_decode (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal) :
    decodeSelection? x (canonicalCollectionSelectionCode x) = (dispatch x).selection := by
  rw [canonicalCollectionSelectionCode_eq_dispatch x payload ledger proposal hstate]
  exact decodeSelection?_map _

/-- Restore the whole canonical dispatch with its original collection frame. -/
theorem dispatch_collection_decode (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hc : cutoffValid (((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time) :
      BoundaryInput p rate)) :
    let b : BoundaryInput p rate := ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time)
    let z := boundaryLocal ⟨b, hc⟩
    (decodeCollectionFullObservation z (collectionFullObservation z) rfl).map
      (fun outcome => DispatchCut.collection payload ledger (assemble z).clock
        (assemble z).cutoffIndex outcome) = some (dispatch x) := by
  dsimp only
  rw [decode_collectionFullObservation_exact]
  exact congrArg some (dispatch_collection x payload ledger proposal hstate hc).symm

theorem canonicalCollectionFullObservation_invalid (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hc : ¬ (1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T)) :
    canonicalCollectionFullObservation x = some (.inl ()) ∧ dispatch x = .invalidCollectionCutoff := by
  classical
  refine ⟨?_, (dispatch_collection_invalid x payload ledger proposal hstate hc).1⟩
  rw [canonicalCollectionFullObservation_collection x payload ledger proposal hstate]
  exact congrArg some (dite_eq_right hc)

def canonicalCollectionDownView (x : RoundInput p rate) :=
  (canonicalCollectionSelectionCode x).map (fun c => c.1)

/-- Collection arm, including the dispatcher's error arm; other phases are absent. -/
def canonicalCollectionArm (x : RoundInput p rate) : Option (Fin p.K) :=
  (canonicalCollectionFullObservation x).map fun observation =>
    optionalElim (coordinatorFallback p) (fun c => c.2.2) (selectionFromBoundary observation)
theorem measurable_canonicalCollectionDownView :
    Measurable (canonicalCollectionDownView (p := p) (rate := rate)) :=
  LaterAssignmentFullOutputMeasurability.measurable_optionMap _ measurable_fst _
    measurable_canonicalCollectionSelectionCode
theorem measurable_canonicalCollectionArm :
    Measurable (canonicalCollectionArm (p := p) (rate := rate)) := by
  let arm : Unit ⊕ FullObservation p rate → Fin p.K := fun o =>
    optionalElim (coordinatorFallback p) (fun c => c.2.2) (selectionFromBoundary o)
  have heq : canonicalCollectionArm = fun x => optionalElim none (fun o => some (arm o))
      (canonicalCollectionFullObservation x) := by
    funext x
    change (canonicalCollectionFullObservation x).map arm = _
    cases canonicalCollectionFullObservation x <;> rfl
  rw [heq]
  exact (measurable_optionalElim _ _
    ((measurable_of_countable (some : Fin p.K → Option (Fin p.K))).comp
      ((measurable_optionalElim _ _ (measurable_snd.comp measurable_snd)).comp
        measurable_selectionFromBoundary))).comp measurable_canonicalCollectionFullObservation

theorem canonicalCollectionDownView_eq_dispatch (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal) :
    canonicalCollectionDownView x = (dispatch x).downView := by
  rw [canonicalCollectionDownView, canonicalCollectionSelectionCode_eq_dispatch x payload ledger proposal hstate]
  unfold DispatchCut.downView
  cases (dispatch x).selection <;> rfl

theorem canonicalCollectionArm_eq_dispatch (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal) :
    canonicalCollectionArm x = some (dispatch x).arm := by
  have hobs := canonicalCollectionFullObservation_collection x payload ledger proposal hstate
  have hselected : canonicalCollectionSelectionCode x = selectionFromBoundary
      (boundaryFullObservation ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time)) := by
    unfold canonicalCollectionSelectionCode
    rw [hobs]
    rfl
  unfold canonicalCollectionArm
  rw [hobs]
  simp only [Option.map_some]
  rw [← hselected, canonicalCollectionSelectionCode_eq_dispatch x payload ledger proposal hstate]
  unfold DispatchCut.arm
  cases (dispatch x).selection <;> rfl

/-- The local collection projection has no fabricated output for other phases. -/
theorem canonicalCollectionFullObservation_absent (x : RoundInput p rate)
    (hphase : collectionCoordinates? (encodeCoordinator x.state.coordinator) = none) :
    canonicalCollectionFullObservation x = none ∧ canonicalCollectionArm x = none := by
  have hobs : canonicalCollectionFullObservation x = none := by
    simp only [canonicalCollectionFullObservation, hphase, mapOptional, Option.map_none]
  exact ⟨hobs, by simp only [canonicalCollectionArm, hobs, Option.map_none]⟩

end Bandits.Support.ReferenceCollectionOutcomeMeasurability

end
