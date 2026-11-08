/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteSuffixInputMeasurability
public import Bandits.Support.ReferenceFirstLiveRecordingReadoutMeasurability

/-!
# Borel domain of the actual later-live readout

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,355-408`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-75`.

This module identifies the exact structural guard of the existing later-live
readout on the actual complete-suffix index subtype. It uses the retained
recorder-call cell and the actual PREPARE operation. It proves a joint Borel
domain and its original-source physical-start event; it proves no readout
coverage, numerical-value measurability, physical queue identity, probability
estimate, or manuscript theorem closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceLiveDispatchOutputMeasurability
open Bandits.Support.ReferenceCoordinatorRecorderCallTrace
open Bandits.Support.FollowerPrepareJointMeasurability

namespace Bandits.Support.ReferenceLaterLiveReadoutDomain

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput p

/-- The actual complete-suffix index subtype, with its inherited source
measurable space. -/
abbrev IndexedSource (k : ℕ) :=
  ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k

/-- The actual status tag produced by PREPARE from this round input. `none`
records dagger; `some status` records an ordinary configuration and its exact
status. -/
def preparedStatusTag (i : Fin (p.m - 1))
    (input : ReferenceActivePhysicalStep.RoundInput p rate) :
    Option ActiveRoundActions.FollowerStatus :=
  ReferenceFirstLiveRecordingReadoutMeasurability.incomingOfferStatus
    (ReferenceUpReceptionMeasurability.incomingOfferIndex
      (ReferenceFirstLiveRecordingReadoutMeasurability.preparedIncomingForInput
        (rate := rate) i id input))

/-- All actual PREPARE follower tags, retaining the ordinary status values. -/
def preparedStatusTags (input : ReferenceActivePhysicalStep.RoundInput p rate) :
    Fin (p.m - 1) → Option ActiveRoundActions.FollowerStatus :=
  fun i => preparedStatusTag rate i input

def incomingOrdinaryBit
    (offer : ReferenceUpReceptionMeasurability.IncomingOfferIndex p rate) : Bool :=
  match offer with
  | .dagger => false
  | .ordinary _ => true

/-- The ordinary bit observed from an actual PREPARE status tag. -/
def preparedOrdinaryTag (i : Fin (p.m - 1))
    (input : ReferenceActivePhysicalStep.RoundInput p rate) : Bool :=
  incomingOrdinaryBit rate (ReferenceUpReceptionMeasurability.incomingOfferIndex
    (ReferenceFirstLiveRecordingReadoutMeasurability.preparedIncomingForInput
      (rate := rate) i id input))

/-- The ordinary/dagger bits for every actual prepared follower. -/
def preparedOrdinaryTags (input : ReferenceActivePhysicalStep.RoundInput p rate) :
    Fin (p.m - 1) → Bool :=
  fun i => preparedOrdinaryTag rate i input

/-- The exact all-followers-ordinary PREPARE guard. -/
def preparedOrdinaryInputAll (input : ReferenceActivePhysicalStep.RoundInput p rate) : Bool :=
  decide (∀ i : Fin (p.m - 1), preparedOrdinaryTag rate i input = true)

/-- The Boolean tag attached to the actual recorder-call cell. Absence of a
selection remains `none`; a selected cell records the strict older-start test
and the cell's actual live bit. -/
def recorderSigmaLiveTag (s : ℕ)
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    Option Bool :=
  (ReferenceCoordinatorRecorderCallTrace.cell code).map fun cell =>
    decide (s < cell.1.1.payload.sigma.val) && cell.2.1

/-- Sum-encoded tag used for the Borel predicate. This is the canonical
Option-to-sum observation, with no selected call represented by `inr ()`. -/
def recorderSigmaLiveTagCode (s : ℕ)
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    Bool ⊕ PUnit.{1} :=
  Equiv.optionEquivSumPUnit.{0, 0} Bool (recorderSigmaLiveTag (rate := rate) s code)

/-- The joint guard on the natural readout comparison argument and the actual
indexed source. It uses the index API's actual record code and full input. -/
def indexedReadoutGuard (k : ℕ)
    (z : ℕ × IndexedSource rate rewards C_star C_h k) : Bool :=
  decide (recorderSigmaLiveTagCode (rate := rate) z.1
    (ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt
      rate rewards C_star C_h k z.2) = (Sum.inl true : Bool ⊕ PUnit.{1})) &&
    preparedOrdinaryInputAll rate
      (ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
        rate rewards C_star C_h k z.2)

/-- The original-source event that the actual record at `k` has a later-live
readout at the source's actual physical start. There is no record outside the
existing suffix index domain. -/
def sourceReadoutDomainAt (k : ℕ) : Set (SourceInput (p := p)) :=
  {source | ∃ hk : k <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length,
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get ⟨k, hk⟩)).isSome = true}

private theorem measurable_preparedOrdinaryTag (i : Fin (p.m - 1)) :
    Measurable (preparedOrdinaryTag rate i) := by
  have hincoming :=
    ReferenceFirstLiveRecordingReadoutMeasurability.measurable_preparedIncomingForInput
      (rate := rate) i id measurable_id
  have hindex :=
    (ReferenceUpReceptionMeasurability.measurable_incomingOfferIndex
      (rate := rate)).comp hincoming
  change Measurable (fun input =>
    incomingOrdinaryBit rate
      (ReferenceUpReceptionMeasurability.incomingOfferIndex
        (ReferenceFirstLiveRecordingReadoutMeasurability.preparedIncomingForInput
          (rate := rate) i id input)))
  exact (measurable_of_countable (incomingOrdinaryBit rate)).comp hindex

private theorem measurable_preparedOrdinaryTags :
    Measurable (preparedOrdinaryTags rate) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_preparedOrdinaryTag rate i

private theorem measurable_preparedOrdinaryInputAll :
    Measurable (preparedOrdinaryInputAll rate) := by
  have htag := measurable_preparedOrdinaryTags rate
  have htrue : MeasurableSet
      {input : ReferenceActivePhysicalStep.RoundInput p rate |
        preparedOrdinaryInputAll rate input = true} := by
    have heq :
        {input : ReferenceActivePhysicalStep.RoundInput p rate |
          preparedOrdinaryInputAll rate input = true} =
          ⋂ i : Fin (p.m - 1),
            {input | preparedOrdinaryTag rate i input = true} := by
      ext input
      simp [preparedOrdinaryInputAll, decide_eq_true_eq]
    rw [heq]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_singleton true).preimage ((measurable_pi_iff.mp htag) i)
  have hfalse : MeasurableSet
      {input : ReferenceActivePhysicalStep.RoundInput p rate |
        preparedOrdinaryInputAll rate input = false} := by
    have heq :
        {input : ReferenceActivePhysicalStep.RoundInput p rate |
          preparedOrdinaryInputAll rate input = false} =
          {input | preparedOrdinaryInputAll rate input ≠ true} := by
      ext input
      cases h : preparedOrdinaryInputAll rate input <;> simp [h]
    rw [heq]
    exact htrue.compl
  intro s hs
  classical
  have hpre :
      {input : ReferenceActivePhysicalStep.RoundInput p rate |
        preparedOrdinaryInputAll rate input ∈ s} =
        (if true ∈ s then {input | preparedOrdinaryInputAll rate input = true} else ∅) ∪
          (if false ∈ s then {input | preparedOrdinaryInputAll rate input = false} else ∅) := by
    ext input
    cases h : preparedOrdinaryInputAll rate input <;> simp [h]
  change MeasurableSet {input : ReferenceActivePhysicalStep.RoundInput p rate |
    preparedOrdinaryInputAll rate input ∈ s}
  rw [hpre]
  by_cases hT : true ∈ s <;> by_cases hF : false ∈ s <;>
    simp [hT, hF, htrue, hfalse]

theorem preparedOrdinaryTag_eq_ordinaryData (i : Fin (p.m - 1))
    (input : ReferenceActivePhysicalStep.RoundInput p rate) :
    preparedOrdinaryTag rate i input =
      (ReferenceLaterLiveNumericalReadout.ordinaryData
        (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
          (ReferenceFirstLiveRecordingReadoutMeasurability.preparedIncomingForInput
            (rate := rate) i id input))).isSome := by
  cases hin : ReferenceFirstLiveRecordingReadoutMeasurability.preparedIncomingForInput
      (rate := rate) i id input <;>
    simp [preparedOrdinaryTag, incomingOrdinaryBit,
      ReferenceUpReceptionMeasurability.incomingOfferIndex,
      FollowerPrepareJointMeasurability.incomingConfigurationToSum,
      FollowerPrepareJointMeasurability.localConfigurationOfIncoming,
      ReferenceLaterLiveNumericalReadout.ordinaryData, hin]

theorem preparedConfiguration_eq_input (r :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) :
    FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
        (ReferenceFirstLiveRecordingReadoutMeasurability.preparedIncomingForInput
          (rate := rate) i id r.input) =
      (r.output.preparation.followers.followers i).configuration := by
  have houtput : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    have h := congrArg
      (fun output : ReferenceActivePhysicalStep.RoundOutput r.input => output.preparation)
      r.output_eq
    simpa [ReferenceActivePhysicalStep.step] using h
  have h := congrArg DeclaredFollowerLocalRound.PreparedRound.configuration
    (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode_reconstruct r.input i)
  simpa [ReferenceFirstLiveRecordingReadoutMeasurability.preparedIncomingForInput,
    ReferenceActivePhysicalStepMeasurability.preparedFollowerCode,
    FollowerVaryingActivationMeasurability.varyingPreparedConfiguration,
    FollowerVaryingActivationMeasurability.varyingPreparedOutput,
    FollowerPrepareJointMeasurability.preparedRoundOfOutput, houtput] using h

/-- The actual PREPARE tags are ordinary at every follower exactly when the
record's literal prepared configurations satisfy the numerical readout's
ordinary-family guard. This is derived from `output_eq`. -/
theorem preparedOrdinary_eq_actualTags (r :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceLaterLiveNumericalReadout.preparedOrdinary r ↔
      preparedOrdinaryInputAll rate r.input = true := by
  constructor
  · intro h
    have hall : ∀ i : Fin (p.m - 1), preparedOrdinaryTag rate i r.input = true := by
      intro i
      have hi := h i
      rw [← preparedConfiguration_eq_input rate r i] at hi
      change preparedOrdinaryTag rate i r.input = true
      rw [preparedOrdinaryTag_eq_ordinaryData rate i r.input]
      exact hi
    simp [preparedOrdinaryInputAll, hall]
  · intro h i
    have hall : ∀ i : Fin (p.m - 1), preparedOrdinaryTag rate i r.input = true := by
      simpa [preparedOrdinaryInputAll] using h
    have hi := hall i
    rw [preparedOrdinaryTag_eq_ordinaryData rate i r.input] at hi
    rw [preparedConfiguration_eq_input rate r i] at hi
    exact hi

private theorem measurable_selectionSigmaTrace :
    Measurable
      (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
        selected.1.payload.sigma.val) := by
  have hview : Measurable
      (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
        (p := p) (rate := rate)) := comap_measurable _
  have hpayload : Measurable
      (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
        selected.1.payload) := measurable_fst.comp (hview.comp measurable_fst)
  have hpayloadObservation : Measurable
      (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
        LaterAssignmentStartMeasurability.payloadObservation selected.1.payload) :=
    (comap_measurable _).comp hpayload
  have hsigma : Measurable
      (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
        (LaterAssignmentStartMeasurability.payloadObservation selected.1.payload).2.1) :=
    measurable_fst.comp (measurable_snd.comp hpayloadObservation)
  exact (measurable_of_countable (fun t : Fin p.T => t.val)).comp hsigma

private theorem measurable_recorderSigmaLiveTagCode (s : ℕ) :
    Measurable (recorderSigmaLiveTagCode (rate := rate) s) := by
  have hcell := ReferenceCoordinatorRecorderCallTrace.measurable_cell
    (p := p) (rate := rate)
  have hentry : Measurable
      (fun pair :
        (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
          (Bool × (Bool × Option (CoordinatorRecordingOperation.Output p)))) ×
        ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
        decide (s < pair.1.1.1.payload.sigma.val) && pair.1.2.1) := by
    have hcoordinates : Measurable (fun pair :
        (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
          (Bool × (Bool × Option (CoordinatorRecordingOperation.Output p)))) ×
        ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
        (pair.1.1.1.payload.sigma.val, pair.1.2.1)) :=
      ((measurable_selectionSigmaTrace rate).comp
        (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_fst))
    exact (measurable_of_countable
      (fun value : ℕ × Bool => decide (s < value.1) && value.2)).comp hcoordinates
  let : MeasurableSpace (Option Bool) :=
    (inferInstance : MeasurableSpace (Bool ⊕ PUnit.{1})).comap
      (Equiv.optionEquivSumPUnit.{0, 0} Bool)
  have hoption : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
      (ReferenceCoordinatorRecorderCallTrace.cell code).map
        (fun cell => decide (s < cell.1.1.payload.sigma.val) && cell.2.1)) :=
    ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun pair => decide (s < pair.1.1.1.payload.sigma.val) && pair.1.2.1)
      hentry (ReferenceCoordinatorRecorderCallTrace.cell (p := p) (rate := rate)) hcell
  change Measurable (fun code :
    ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
      Equiv.optionEquivSumPUnit.{0, 0} Bool
        ((ReferenceCoordinatorRecorderCallTrace.cell code).map
          (fun cell => decide (s < cell.1.1.payload.sigma.val) && cell.2.1)))
  exact measurable_comap_iff.mp hoption

/-- The joint Option-valued Boolean observation of the exact recorder-call
sigma/live guard is Borel in the countable comparison argument and full code. -/
theorem measurable_recorderSigmaLiveTagCode_joint :
    Measurable (fun z : ℕ ×
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
        recorderSigmaLiveTagCode (rate := rate) z.1 z.2) :=
  measurable_from_prod_countable_right (fun s => measurable_recorderSigmaLiveTagCode (rate := rate) s)

/-- The recorder-call tag equals `some true` precisely for an existing
selection whose retained strict-start comparison and actual live bit both
pass. The stored recording result and enabled bit are retained but do not
enter this structural guard. -/
theorem recorderSigmaLiveTag_eq_true_iff (s : ℕ)
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    recorderSigmaLiveTag (rate := rate) s code = some true ↔
      ∃ selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate,
        ReferenceCoordinatorRecorderCallTrace.selection code = some selected ∧
          s < selected.1.payload.sigma.val ∧
          ReferenceCoordinatorRecorderCallTrace.live code selected = true := by
  classical
  unfold recorderSigmaLiveTag
  cases hselection : ReferenceCoordinatorRecorderCallTrace.selection code with
  | none => simp [ReferenceCoordinatorRecorderCallTrace.cell, hselection]
  | some selected =>
      simp [ReferenceCoordinatorRecorderCallTrace.cell, hselection,
        Bool.and_eq_true, decide_eq_true_eq]

/-- The sum code's true branch is exactly the Option tag `some true`. -/
theorem recorderSigmaLiveTagCode_eq_true_iff (s : ℕ)
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    recorderSigmaLiveTagCode (rate := rate) s code = Sum.inl true ↔
      ∃ selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate,
        ReferenceCoordinatorRecorderCallTrace.selection code = some selected ∧
          s < selected.1.payload.sigma.val ∧
          ReferenceCoordinatorRecorderCallTrace.live code selected = true := by
  have hcode : recorderSigmaLiveTagCode (rate := rate) s code = Sum.inl true ↔
      recorderSigmaLiveTag (rate := rate) s code = some true := by
    cases htag : recorderSigmaLiveTag (rate := rate) s code <;>
      simp [recorderSigmaLiveTagCode, htag, Equiv.optionEquivSumPUnit]
  exact hcode.trans (recorderSigmaLiveTag_eq_true_iff (rate := rate) s code)

theorem roundRecordSelection_eq_dispatch (r :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    r.output.preparation.coordinator.selection =
      (ReferenceActivePhysicalStep.dispatch r.input).selection := by
  have h := congrArg
    (fun output : ReferenceActivePhysicalStep.RoundOutput r.input =>
      output.preparation.coordinator.selection) r.output_eq
  simpa [ReferenceActivePhysicalStep.step, ReferenceActivePhysicalStep.prepare] using h

theorem recorderSigmaLiveTag_actual_iff (s : ℕ) (r :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    recorderSigmaLiveTagCode (rate := rate) s
        (ReferenceActiveHorizonMeasurability.roundRecordCode r) = Sum.inl true ↔
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        r.output.preparation.coordinator.selection = some selected ∧
          s < selected.view.payload.sigma.val ∧
          CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
            selected.view.cutoff r.input.time := by
  have hselectionCode :
      ReferenceCoordinatorRecorderCallTrace.selection
          (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
        r.output.preparation.coordinator.selection.map
          ReferenceLiveDispatchOutputMeasurability.encodeSelection := by
    rw [ReferenceCoordinatorRecorderCallTrace.selection]
    rw [(ReferenceActiveHorizonMeasurability.roundRecordCode_front r).1]
    rw [← roundRecordSelection_eq_dispatch rate r]
  classical
  rw [recorderSigmaLiveTagCode_eq_true_iff (rate := rate)]
  constructor
  · rintro ⟨encoded, hencoded, hsigma, hlive⟩
    rw [hselectionCode] at hencoded
    cases hactual : r.output.preparation.coordinator.selection with
    | none => simp [hactual] at hencoded
    | some selected =>
        simp [hactual] at hencoded
        subst encoded
        refine ⟨selected, rfl, ?_, ?_⟩
        · simpa [ReferenceLiveDispatchOutputMeasurability.encodeSelection] using hsigma
        · have hliveEq := ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
            (ReferenceActiveHorizonMeasurability.roundRecordCode r)
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected)
            r.input.time rfl
          have hliveEncoded :
              CoordinatorLocalArmChoice.assignmentIsLive
                (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected).1.payload
                (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected).1.cutoff
                r.input.time := by
            apply decide_eq_true_eq.mp
            rw [← hliveEq]
            exact hlive
          simpa [ReferenceLiveDispatchOutputMeasurability.encodeSelection] using hliveEncoded
  · rintro ⟨selected, hselection, hsigma, hlive⟩
    refine ⟨ReferenceLiveDispatchOutputMeasurability.encodeSelection selected,
      ?_, ?_, ?_⟩
    · rw [hselectionCode, hselection]
      rfl
    · simpa [ReferenceLiveDispatchOutputMeasurability.encodeSelection] using hsigma
    · have hliveEq := ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
        (ReferenceActiveHorizonMeasurability.roundRecordCode r)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected)
        r.input.time rfl
      classical
      have hdecision : decide
          (CoordinatorLocalArmChoice.assignmentIsLive
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected).1.payload
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected).1.cutoff
            r.input.time) = true :=
        decide_eq_true_eq.mpr (by
          simpa [ReferenceLiveDispatchOutputMeasurability.encodeSelection] using hlive)
      rw [hliveEq]
      exact hdecision

/-- Exact recorder-trace and actual PREPARE tag factorization of the literal
later-live readout guard. Every dispatcher terminal/failure branch is covered
by the retained selection cell, and arbitrary dagger followers fail only the
actual all-ordinary tag test. -/
theorem laterLiveReadout_isSome_iff_traceGuard (s : ℕ) (r :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
      (ReferenceLaterLiveNumericalReadout.laterLiveReadout s r).isSome = true ↔
      recorderSigmaLiveTagCode (rate := rate) s
          (ReferenceActiveHorizonMeasurability.roundRecordCode r) = (Sum.inl true : Bool ⊕ PUnit.{1}) ∧
        preparedOrdinaryInputAll rate r.input = true := by
  apply (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain s r).trans
  unfold ReferenceLaterLiveNumericalReadout.laterLiveDomain
  constructor
  · rintro ⟨selected, hselection, hsigma, hlive, hordinary⟩
    exact ⟨(recorderSigmaLiveTag_actual_iff rate s r).2
      ⟨selected, hselection, hsigma, hlive⟩,
      (preparedOrdinary_eq_actualTags rate r).mp hordinary⟩
  · rintro ⟨htrace, hordinary⟩
    obtain ⟨selected, hselection, hsigma, hlive⟩ :=
      (recorderSigmaLiveTag_actual_iff rate s r).1 htrace
    exact ⟨selected, hselection, hsigma, hlive,
      (preparedOrdinary_eq_actualTags rate r).mpr hordinary⟩

/-- The requested structural factorization directly on actual records:
selection exists, the readout argument is strictly before its selected sigma,
the actual assignment is live, and all actual PREPARE tags are ordinary. -/
theorem laterLiveReadout_isSome_iff_actualGuard (s : ℕ) (r :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout s r).isSome = true ↔
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        r.output.preparation.coordinator.selection = some selected ∧
          s < selected.view.payload.sigma.val ∧
          CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
            selected.view.cutoff r.input.time ∧
          (∀ i : Fin (p.m - 1), preparedOrdinaryTag rate i r.input = true) := by
  constructor
  · intro hreadout
    have hguard := (laterLiveReadout_isSome_iff_traceGuard rate s r).mp hreadout
    obtain ⟨selected, hselection, hsigma, hlive⟩ :=
      (recorderSigmaLiveTag_actual_iff rate s r).mp hguard.1
    have htags : ∀ i : Fin (p.m - 1), preparedOrdinaryTag rate i r.input = true := by
      simpa [preparedOrdinaryInputAll] using hguard.2
    exact ⟨selected, hselection, hsigma, hlive, htags⟩
  · rintro ⟨selected, hselection, hsigma, hlive, htags⟩
    have hall : preparedOrdinaryInputAll rate r.input = true := by
      simp [preparedOrdinaryInputAll, htags]
    exact (laterLiveReadout_isSome_iff_traceGuard rate s r).mpr
      ⟨(recorderSigmaLiveTag_actual_iff rate s r).mpr
        ⟨selected, hselection, hsigma, hlive⟩, hall⟩

/-- Exact guard factorization for the actual `k`th suffix record, using only
the admitted input and code projections of the same record. -/
theorem actualIndexedReadout_isSome_iff_guard (k s : ℕ)
    (x : IndexedSource rate rewards C_star C_h k) :
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout s
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate x.val rewards C_star C_h).get ⟨k, x.property⟩)).isSome = true ↔
      recorderSigmaLiveTagCode (rate := rate) s
        (ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt
          rate rewards C_star C_h k x) = (Sum.inl true : Bool ⊕ PUnit.{1}) ∧
      preparedOrdinaryInputAll rate
        (ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
          rate rewards C_star C_h k x) = true := by
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate x.val rewards C_star C_h).get ⟨k, x.property⟩
  have h := laterLiveReadout_isSome_iff_traceGuard rate s record
  simpa [record,
    ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt,
    ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt] using h

private theorem indexedReadoutGuard_eq_true_iff (k : ℕ)
    (z : ℕ × IndexedSource rate rewards C_star C_h k) :
    indexedReadoutGuard rate rewards C_star C_h k z = true ↔
      recorderSigmaLiveTagCode (rate := rate) z.1
          (ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt
            rate rewards C_star C_h k z.2) = (Sum.inl true : Bool ⊕ PUnit.{1}) ∧
        preparedOrdinaryInputAll rate
          (ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
            rate rewards C_star C_h k z.2) = true := by
  change decide (_ = (Sum.inl true : Bool ⊕ PUnit.{1})) && _ = true ↔ _
  constructor
  · intro h
    rcases Bool.and_eq_true_iff.mp h with ⟨htrace, hordinary⟩
    exact ⟨decide_eq_true_eq.mp htrace, hordinary⟩
  · rintro ⟨htrace, hordinary⟩
    apply Bool.and_eq_true_iff.mpr
    exact ⟨decide_eq_true_eq.mpr htrace, hordinary⟩

private theorem measurableSet_indexedReadoutGuard (k : ℕ) :
    MeasurableSet {z : ℕ × IndexedSource rate rewards C_star C_h k |
      indexedReadoutGuard rate rewards C_star C_h k z = true} := by
  let actualCode := ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt
    rate rewards C_star C_h k
  let actualInput := ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
    rate rewards C_star C_h k
  have hcode : Measurable (fun z : ℕ × IndexedSource rate rewards C_star C_h k =>
      actualCode z.2) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_actualRecordCodeAt
      rate rewards C_star C_h k).comp measurable_snd
  have hinput : Measurable (fun z : ℕ × IndexedSource rate rewards C_star C_h k =>
      actualInput z.2) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_actualRoundInputAt
      rate rewards C_star C_h k).comp measurable_snd
  have hordinary : MeasurableSet {z : ℕ × IndexedSource rate rewards C_star C_h k |
      preparedOrdinaryInputAll rate (actualInput z.2) = true} := by
    have heq : {z : ℕ × IndexedSource rate rewards C_star C_h k |
        preparedOrdinaryInputAll rate (actualInput z.2) = true} =
        ⋂ i : Fin (p.m - 1), {z | preparedOrdinaryTag rate i (actualInput z.2) = true} := by
      ext z
      simp [preparedOrdinaryInputAll]
    rw [heq]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_singleton true).preimage
        ((measurable_preparedOrdinaryTag rate i).comp hinput)
  have htrace (s : ℕ) : MeasurableSet {z : ℕ × IndexedSource rate rewards C_star C_h k |
      recorderSigmaLiveTagCode (rate := rate) s (actualCode z.2) = (Sum.inl true : Bool ⊕ PUnit.{1})} := by
    let : MeasurableSingletonClass (Bool ⊕ PUnit.{1}) := ⟨fun tag => by
      cases tag with
      | inl value =>
          simpa only [Set.image_singleton] using
            (measurableSet_singleton value).inl_image
      | inr value =>
          simpa only [Set.image_singleton] using
            (measurableSet_singleton value).inr_image⟩
    exact (measurableSet_singleton (Sum.inl true : Bool ⊕ PUnit.{1})).preimage
      ((measurable_recorderSigmaLiveTagCode (rate := rate) s).comp hcode)
  have hsplit : {z : ℕ × IndexedSource rate rewards C_star C_h k |
      indexedReadoutGuard rate rewards C_star C_h k z = true} =
      ⋃ s : ℕ, {z | z.1 = s ∧
        recorderSigmaLiveTagCode (rate := rate) s (actualCode z.2) = (Sum.inl true : Bool ⊕ PUnit.{1}) ∧
        preparedOrdinaryInputAll rate (actualInput z.2) = true} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      have hguard := (indexedReadoutGuard_eq_true_iff rate rewards C_star C_h k z).mp h
      exact ⟨z.1, rfl, hguard.1, hguard.2⟩
    · rintro ⟨s, hzs, htrace, hordinary⟩
      subst s
      exact (indexedReadoutGuard_eq_true_iff rate rewards C_star C_h k z).mpr
        ⟨htrace, hordinary⟩
  rw [hsplit]
  exact MeasurableSet.iUnion fun s =>
    ((measurableSet_singleton s).preimage measurable_fst).inter
      ((htrace s).inter hordinary)

/-- Joint Borelness in the natural strict-start argument and every original
source factor on the genuine complete-suffix index domain. -/
theorem measurableSet_indexedReadoutDomain (k : ℕ) : MeasurableSet
    {z : ℕ × IndexedSource rate rewards C_star C_h k |
      (ReferenceLaterLiveNumericalReadout.laterLiveReadout z.1
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z.2.val rewards C_star C_h).get ⟨k, z.2.property⟩)).isSome = true} := by
  have hset :
      {z : ℕ × IndexedSource rate rewards C_star C_h k |
        (ReferenceLaterLiveNumericalReadout.laterLiveReadout z.1
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z.2.val rewards C_star C_h).get ⟨k, z.2.property⟩)).isSome = true} =
      {z | indexedReadoutGuard rate rewards C_star C_h k z = true} := by
    ext z
    exact (actualIndexedReadout_isSome_iff_guard rate rewards C_star C_h k z.1 z.2).trans
      (indexedReadoutGuard_eq_true_iff rate rewards C_star C_h k z).symm
  rw [hset]
  exact measurableSet_indexedReadoutGuard rate rewards C_star C_h k

/-- Fixed-`s` Borelness on the same actual indexed source subtype. -/
theorem measurableSet_indexedReadoutDomain_fixed (s k : ℕ) : MeasurableSet
    {x : IndexedSource rate rewards C_star C_h k |
      (ReferenceLaterLiveNumericalReadout.laterLiveReadout s
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate x.val rewards C_star C_h).get ⟨k, x.property⟩)).isSome = true} := by
  have hslice : Measurable (fun x : IndexedSource rate rewards C_star C_h k => (s, x)) :=
    measurable_const.prodMk measurable_id
  have hguard := (measurableSet_indexedReadoutGuard rate rewards C_star C_h k).preimage hslice
  have hset :
      {x : IndexedSource rate rewards C_star C_h k |
        (ReferenceLaterLiveNumericalReadout.laterLiveReadout s
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate x.val rewards C_star C_h).get ⟨k, x.property⟩)).isSome = true} =
      {x | indexedReadoutGuard rate rewards C_star C_h k (s, x) = true} := by
    ext x
    exact (actualIndexedReadout_isSome_iff_guard rate rewards C_star C_h k s x).trans
      (indexedReadoutGuard_eq_true_iff rate rewards C_star C_h k (s, x)).symm
  rw [hset]
  exact hguard

/-- The original-source physical-start event is Borel. It is lifted from the
actual indexed subtype image using the exact joint guard and the existing
physical-start measurability theorem. -/
theorem measurableSet_sourceReadoutDomainAt (k : ℕ) :
    MeasurableSet (sourceReadoutDomainAt rate rewards C_star C_h k) := by
  let indexDomain : Set (SourceInput (p := p)) :=
    {source | k < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length}
  have hindex : MeasurableSet indexDomain :=
    ReferenceCompleteSuffixInputMeasurability.measurableSet_indexDomain
      rate rewards C_star C_h k
  let indexedSuccess : Set (IndexedSource rate rewards C_star C_h k) :=
    {x | (ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate x.val rewards C_star C_h).get ⟨k, x.property⟩)).isSome = true}
  have hsuccess : MeasurableSet indexedSuccess := by
    have hphysicalStart : Measurable
        (fun x : IndexedSource rate rewards C_star C_h k =>
          ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h) :=
      (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
        rate rewards C_star C_h).comp measurable_subtype_coe
    have hcoordinate : Measurable
        (fun x : IndexedSource rate rewards C_star C_h k =>
          (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h, x)) :=
      hphysicalStart.prodMk measurable_id
    have hguard : MeasurableSet {x : IndexedSource rate rewards C_star C_h k |
        indexedReadoutGuard rate rewards C_star C_h k
          (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h, x) = true} := by
      exact (measurableSet_indexedReadoutGuard rate rewards C_star C_h k).preimage hcoordinate
    have heq : indexedSuccess = {x |
        indexedReadoutGuard rate rewards C_star C_h k
          (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h, x) = true} := by
      ext x
      exact (actualIndexedReadout_isSome_iff_guard rate rewards C_star C_h k
        (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h) x).trans
        (indexedReadoutGuard_eq_true_iff rate rewards C_star C_h k
          (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h, x)).symm
    rw [heq]
    exact hguard
  have himage : MeasurableSet (((↑) :
      IndexedSource rate rewards C_star C_h k → SourceInput (p := p)) '' indexedSuccess) :=
    hindex.subtype_image hsuccess
  have hdomain : sourceReadoutDomainAt rate rewards C_star C_h k =
      ((↑) : IndexedSource rate rewards C_star C_h k → SourceInput (p := p)) '' indexedSuccess := by
    ext source
    constructor
    · rintro ⟨hk, hsuccess⟩
      exact ⟨⟨source, hk⟩, hsuccess, rfl⟩
    · rintro ⟨x, hsuccess, rfl⟩
      exact ⟨x.property, hsuccess⟩
  rw [hdomain]
  exact himage

end Bandits.Support.ReferenceLaterLiveReadoutDomain

end
