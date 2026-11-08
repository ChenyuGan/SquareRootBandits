/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceRankInstallationSourceKernelComposition
public import Bandits.Support.ReferenceRankInstallationPostUpdateProposalLaw

/-!
# Original joint recorder, reserved-FAST, and whole-update law

At an arbitrary actual rank installation, the recorder and reserved FAST draw
remain one correlated source pair. The complete all-arm numerical update is a
literal readout of that pair and the original strict-past state; the selected
proposal bit is factored only after forming this common observation.

Source evidence: ZIP4 `06_interruptions.tex:381-426` and
`04_slow_fast_learner.tex:142-215,323-390`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceRankInstallationRecorderFoundation
open Bandits.Support.ReferenceFirstLivePostUpdateProposalLaw

namespace Bandits.Support.ReferenceRankInstallationCommonUpdateJointLaw

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  ReferenceRankInstallationRecorderFoundation.SourceInput p
abbrev History (p : ConstructorDimensions.Parameters) :=
  ReferenceRankInstallationRecorderFoundation.History p
abbrev Remainder (p : ConstructorDimensions.Parameters) :=
  ReferenceLaterOptionalControlResampling.ControlRemainder p
abbrev Pair (p : ConstructorDimensions.Parameters) :=
  ReferenceRankInstallationRecorderFastSourceLaw.RecorderFastOutput p
abbrev PairUpdate (p : ConstructorDimensions.Parameters) :=
  Pair p × Option (NumericalUpdateFields p)

local notation "installEvent" =>
  ReferenceRankInstallationRecorderFoundation.installationEvent rate rewards C_star C_h
local notation "viewAt" =>
  ReferenceRankInstallationRecorderFoundation.actualInstallationView rate rewards C_star C_h
local notation "historyAt" =>
  ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h
local notation "actualPair" =>
  ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h
local notation "beforeAt" =>
  ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
    rate rewards C_star C_h

attribute [local instance]
  ReferenceRankInstallationRecorderFoundation.sourceInputMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.optionMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.optionSingleton
  ReferenceRankInstallationRecorderFoundation.outcomeMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.outcomeDiscreteMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.outcomeOptionMeasurableSpace
  ReferenceRankInstallationRecorderFastLaw.reservedMarkerMeasurableSpace

/-- The all-arm raw-arrival vector determined by the recorder coordinate.
Outer absence remains absent; a present bottom recorder emits present zero
raw arrivals. -/
def rawArrivalsFromPair (t : Fin p.T)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (q : Pair p) : Option (Fin p.K → ℕ) :=
  q.1.map fun o a => if o = some a then
    Nat.floor ((D p : ℝ) * rate.eta.val *
      (((rewards t a).val : ℝ) / (D p : ℝ)) / v.payload.rate a) else 0

/-- Apply the literal queue update to the actual strict-past state and the
recorder-derived whole-arm raw vector. -/
def updateFromPair (t : Fin p.T)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (before : Option (ReferenceRankInstallationPostUpdateProposalLaw.NumericalState p))
    (q : Pair p) : Option (NumericalUpdateFields p) :=
  ReferenceRankInstallationPostUpdateProposalLaw.numericalUpdateFromReadouts rate
    before (rawArrivalsFromPair rate rewards t v q)

/-- The correlated finite recorder/FAST law pushed through the complete
numerical-update readout. -/
def commonUpdateKernel (t : Fin p.T)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights)
    (before : Option (ReferenceRankInstallationPostUpdateProposalLaw.NumericalState p)) :
    Measure (PairUpdate p) :=
  (ReferenceRankInstallationSourceKernelComposition.installationRecorderFastOutputKernel
    rate t v valid).map (fun q => (q, updateFromPair rate rewards t v before q))

/-- The literal reconstructed pair/update observer for every complete
original control remainder. -/
def reconstructedPairUpdate (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T)
    (h : History p)
    (d : Remainder p) : PairUpdate p :=
  let z := ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder
    t h d
  let q := ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
    rate rewards C_star C_h t h d
  (q, ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
    rate rewards C_star C_h control0 t z)

/-- The finite pair-to-update map is Borel on the complete pair carrier,
including outer absence and present bottom. -/
theorem measurable_updateFromPair (t : Fin p.T)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (before : Option (ReferenceRankInstallationPostUpdateProposalLaw.NumericalState p)) :
    Measurable (fun q : Pair p => updateFromPair rate rewards t v before q) := by
  exact measurable_of_countable _

/-- Measurability of the finite correlated kernel after the deterministic
whole-update readout. -/
theorem measurable_commonUpdateKernelMap (t : Fin p.T)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (before : Option (ReferenceRankInstallationPostUpdateProposalLaw.NumericalState p)) :
    Measurable (fun q : Pair p =>
      (q, updateFromPair rate rewards t v before q)) := by
  exact measurable_id.prodMk (measurable_updateFromPair rate rewards t v before)

/-- Replacing the complete current control remainder preserves the literal
strict-past numerical state, since its source prefix is idempotent. -/
theorem reconstructedNumericalBefore_eq_original
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p)
    (d : Remainder p) :
    ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t
        (ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder
          t (historyAt control0 k t z) d) =
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t z := by
  change ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rate rewards C_star C_h t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder
          t (historyAt control0 k t z) d)) = _
  change _ =
    ReferenceFirstCollectionCurrentRetainedGate.prefixReadout? rate rewards C_star C_h t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
  rw [ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder,
    ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current]
  change ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rate rewards C_star C_h t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)) = _
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
    control0 t.val t.val le_rfl z]

/-- On the installation event, the original all-arm update is exactly the
literal readout from the recorder coordinate, selected view, and the source's
own strict-past state. The raw formula retains present zero and distinguishes
outer absence. -/
theorem actualInstallationNumericalUpdate_eq_updateFromPair
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p)
    (hz : z ∈ installEvent k t)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (hv : viewAt t z = some v) :
    ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
        rate rewards C_star C_h control0 t z =
      updateFromPair rate rewards t v
        (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
          rate rewards C_star C_h control0 t z) (actualPair t z) := by
  obtain ⟨v', o, hv', hmarker, hraw⟩ :=
    ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_rawArrivals_formula
      rate rewards C_star C_h control0 k t z hz
  have hvEq : v' = v := Option.some.inj (hv'.symm.trans hv)
  subst v'
  have hpairMarker : (actualPair t z).1 = some o := by
    change ReferenceRankInstallationRecorderFoundation.actualMarker
      rate rewards C_star C_h t z = some o
    exact hmarker
  have hrawArrivals :
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationRawArrivals
          rate rewards C_star C_h t z = rawArrivalsFromPair rate rewards t v (actualPair t z) := by
    simp only [ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationRawArrivals]
    rw [hraw]
    simp [rawArrivalsFromPair, hpairMarker]
  obtain ⟨before, c, henabled, hbefore, hstepRaw, hstepUpdate⟩ :=
    ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_numericalUpdate_eq_step
      rate rewards C_star C_h control0 k t z hz
  have hpairRaw : rawArrivalsFromPair rate rewards t v (actualPair t z) =
      some (RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c) :=
    hrawArrivals.symm.trans hstepRaw
  have hpairUpdate : updateFromPair rate rewards t v
      (some (before.registers, before.overflow, before.records)) (actualPair t z) =
      some
        { raw := RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
          beforeRegisters := before.registers
          beforeOverflow := before.overflow
          beforeRecords := before.records
          accepted := RecordedQueueRun.acceptedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c
          service := fun j => RecordedQueueRun.recordService (4 * rate.n)
            (before.registers j)
            (RecordedQueueRun.acceptedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c j)
          afterRegisters := (RecordedQueueRun.step
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c).registers
          afterOverflow := (RecordedQueueRun.step
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c).overflow
          afterRecords := (RecordedQueueRun.step
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c).records} := by
    unfold updateFromPair ReferenceRankInstallationPostUpdateProposalLaw.numericalUpdateFromReadouts
    rw [hpairRaw]
    exact congrArg some
      (ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields_eq_step
        rate before c henabled)
  calc
    _ = some
        { raw := RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
          beforeRegisters := before.registers
          beforeOverflow := before.overflow
          beforeRecords := before.records
          accepted := RecordedQueueRun.acceptedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c
          service := fun j => RecordedQueueRun.recordService (4 * rate.n)
            (before.registers j)
            (RecordedQueueRun.acceptedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c j)
          afterRegisters := (RecordedQueueRun.step
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c).registers
          afterOverflow := (RecordedQueueRun.step
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c).overflow
          afterRecords := (RecordedQueueRun.step
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c).records} := hstepUpdate
    _ = updateFromPair rate rewards t v
        (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
          rate rewards C_star C_h control0 t z) (actualPair t z) := by
      rw [hbefore]
      exact hpairUpdate.symm

/-- The actual common observer is recovered for every complete remainder from
the source reconstruction, not from an assumed observer identity. -/
theorem reconstructedObserver_eq_commonReadout
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p)
    (hz : z ∈ installEvent k t) :
    ∃ (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
      (_valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
        v.complementWeights),
      viewAt t z = some v ∧
      ∀ d : Remainder p,
        let h := historyAt control0 k t z
        let x := ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder
          t h d
        x ∈ installEvent k t ∧
        ReferenceRankInstallationPostUpdateProposalLaw.actualRankPreProposalObserver
            rate rewards C_star C_h control0 t x =
          (some v,
            (ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
                rate rewards C_star C_h t h d,
              updateFromPair rate rewards t v
                (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
                  rate rewards C_star C_h control0 t z)
                (ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
                  rate rewards C_star C_h t h d))) := by
  obtain ⟨v, valid, hv, _hactual, _hrestore, hall⟩ :=
    ReferenceRankInstallationSourceKernelComposition.actualPairFromHistoryRemainder_sameSlice_of_installation
      rate rewards C_star C_h control0 k t z hz
  refine ⟨v, valid, hv, ?_⟩
  intro d
  let h := historyAt control0 k t z
  let x := ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder
    t h d
  have hdata := hall d
  have hx : x ∈ installEvent k t := by
    simpa [x, h] using hdata.1
  have hvx : viewAt t x = some v := by
    simpa [x, h] using hdata.2.1
  have hpair : actualPair t x =
      ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
        rate rewards C_star C_h t h d := rfl
  have hbefore := reconstructedNumericalBefore_eq_original
    rate rewards C_star C_h control0 k t z d
  have hupdate := actualInstallationNumericalUpdate_eq_updateFromPair
    rate rewards C_star C_h control0 k t x hx v hvx
  unfold ReferenceRankInstallationPostUpdateProposalLaw.actualRankPreProposalObserver
  dsimp only [h, x]
  rw [hvx, hpair, hupdate, hbefore]
  exact ⟨hx, rfl⟩

/-- The all-remainder observer comparison and the original enabled queue-step
witness use the same actual view and the same strict-past state. -/
theorem reconstructedObserver_and_originalQueueStep
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ installEvent k t) :
    ∃ (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
      (_valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
        v.complementWeights)
      (before : RecordedQueueRun.RunState p.K)
      (c : RecordedQueueRun.RoundInput p.K),
      viewAt t z = some v ∧ c.enabled = true ∧
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
          rate rewards C_star C_h control0 t z =
        some (before.registers, before.overflow, before.records) ∧
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationRawArrivals
          rate rewards C_star C_h t z =
        some (RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c) ∧
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 t z =
        some
          { raw := RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
            beforeRegisters := before.registers
            beforeOverflow := before.overflow
            beforeRecords := before.records
            accepted := RecordedQueueRun.acceptedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c
            service := fun j => RecordedQueueRun.recordService (4 * rate.n) (before.registers j)
              (RecordedQueueRun.acceptedRecord
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c j)
            afterRegisters := (RecordedQueueRun.step
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c).registers
            afterOverflow := (RecordedQueueRun.step
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c).overflow
            afterRecords := (RecordedQueueRun.step
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) before c).records } ∧
      ∀ d : Remainder p,
        let h := historyAt control0 k t z
        let x := ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder
          t h d
        x ∈ installEvent k t ∧
        ReferenceRankInstallationPostUpdateProposalLaw.actualRankPreProposalObserver
            rate rewards C_star C_h control0 t x =
          (some v,
            (ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
                rate rewards C_star C_h t h d,
              updateFromPair rate rewards t v
                (some (before.registers, before.overflow, before.records))
                (ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
                  rate rewards C_star C_h t h d))) := by
  obtain ⟨v, valid, hv, hall⟩ := reconstructedObserver_eq_commonReadout
    rate rewards C_star C_h control0 k t z hz
  obtain ⟨before, c, henabled, hbefore, hraw, hupdate⟩ :=
    ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_numericalUpdate_eq_step
      rate rewards C_star C_h control0 k t z hz
  refine ⟨v, valid, before, c, hv, henabled, hbefore, hraw, hupdate, ?_⟩
  intro d
  obtain ⟨hx, hobs⟩ := hall d
  rw [hbefore] at hobs
  exact ⟨hx, hobs⟩

/-- The literal coefficient obtained by reconstructing the whole original
source from each complete history/remainder pair and reading its pair and
whole numerical update. -/
def sourceLawCommonUpdateTestCoefficient
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (h : History p) (B : Set (PairUpdate p)) : ENNReal := by
  classical
  exact ∫⁻ d, if reconstructedPairUpdate rate rewards C_star C_h control0 t h d ∈ B
    then 1 else 0 ∂(ReferenceLaterOptionalControlResampling.controlRemainderLaw p)

/-- The reconstructed pair/update map is Borel on the literal history and
complete remainder carrier. -/
theorem measurable_reconstructedPairUpdate
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable (fun q : History p × Remainder p =>
      reconstructedPairUpdate rate rewards C_star C_h control0 t q.1 q.2) := by
  have hs := ReferenceRankInstallationRecorderFastSourceLaw.measurable_sourceFromHistoryRemainder
    t
  have hp := ReferenceRankInstallationRecorderFastSourceLaw.measurable_actualPairFromHistoryRemainder
    rate rewards C_star C_h t
  have hu := ReferenceRankInstallationPostUpdateProposalLaw.measurable_actualInstallationNumericalUpdate
    rate rewards C_star C_h control0 t
  exact hp.prodMk (hu.comp hs)

/-- The history coefficient is Borel by integrating the literal measurable
reconstruction over the original, unreduced remainder law. -/
theorem measurable_sourceLawCommonUpdateTestCoefficient
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (B : Set (PairUpdate p)) (hB : MeasurableSet B) :
    Measurable (fun h : History p =>
      sourceLawCommonUpdateTestCoefficient rate rewards C_star C_h control0 t h B) := by
  classical
  let f : History p × Remainder p → ENNReal := fun q =>
    if reconstructedPairUpdate rate rewards C_star C_h control0 t q.1 q.2 ∈ B
      then 1 else 0
  have hpre : MeasurableSet {q : History p × Remainder p |
      reconstructedPairUpdate rate rewards C_star C_h control0 t q.1 q.2 ∈ B} :=
    hB.preimage (measurable_reconstructedPairUpdate rate rewards C_star C_h control0 t)
  have hf : Measurable f := Measurable.ite hpre measurable_const measurable_const
  change Measurable (fun h : History p =>
    ∫⁻ d, f (h, d) ∂(ReferenceLaterOptionalControlResampling.controlRemainderLaw p))
  exact hf.lintegral_prod_right'

/-- On an actual history, the complete-remainder coefficient is the original
correlated recorder/FAST kernel pushed through the exact all-arm update map.
The source producer supplies the original prefix and complement-weight
provenance used by that kernel. -/
theorem sourceLawCommonUpdateTestCoefficient_eq_kernel
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ installEvent k t)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) (hv : viewAt t z = some v)
    (B : Set (PairUpdate p)) (hB : MeasurableSet B) :
    sourceLawCommonUpdateTestCoefficient rate rewards C_star C_h control0 t
        (historyAt control0 k t z) B =
      commonUpdateKernel rate rewards t v valid
        (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
          rate rewards C_star C_h control0 t z) B := by
  classical
  let h := historyAt control0 k t z
  let before := ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
    rate rewards C_star C_h control0 t z
  let readout := fun q : Pair p => (q, updateFromPair rate rewards t v before q)
  let pairTest := readout ⁻¹' B
  have hreadout : Measurable readout :=
    measurable_commonUpdateKernelMap rate rewards t v before
  have hpairTest : MeasurableSet pairTest := hB.preimage hreadout
  obtain ⟨v₀, valid₀, hv₀, _hactual, _hrestore, hall⟩ :=
    ReferenceRankInstallationSourceKernelComposition.actualPairFromHistoryRemainder_sameSlice_of_installation
      rate rewards C_star C_h control0 k t z hz
  have hvEq : v₀ = v := Option.some.inj (hv₀.symm.trans hv)
  subst v₀
  have hvalidEq : valid₀ = valid := Subsingleton.elim _ _
  subst valid₀
  have hcoeff :
      sourceLawCommonUpdateTestCoefficient rate rewards C_star C_h control0 t h B =
        ReferenceRankInstallationRecorderFastSourceLaw.sourceLawTestCoefficient
          rate rewards C_star C_h t h pairTest := by
    unfold sourceLawCommonUpdateTestCoefficient
      ReferenceRankInstallationRecorderFastSourceLaw.sourceLawTestCoefficient
    apply lintegral_congr
    intro d
    have hdata := hall d
    let x := ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder
      t h d
    let q := ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
      rate rewards C_star C_h t h d
    have hx : x ∈ installEvent k t := by simpa [x, h] using hdata.1
    have hvx : viewAt t x = some v := by simpa [x, h] using hdata.2.1
    have hcommon := reconstructedObserver_eq_commonReadout
      rate rewards C_star C_h control0 k t z hz
    obtain ⟨v', _valid', hvz, hallObserver⟩ := hcommon
    have hvEq' : v' = v := Option.some.inj (hvz.symm.trans hv)
    subst v'
    have hobs := hallObserver d
    have hupdate :
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
            rate rewards C_star C_h control0 t x =
          updateFromPair rate rewards t v before q := by
      have hproj := congrArg
        (fun o : ReferenceRankInstallationPostUpdateProposalLaw.Observer p rate.eta => o.2.2)
        hobs.2
      simpa [ReferenceRankInstallationPostUpdateProposalLaw.actualRankPreProposalObserver,
        h, x, q, before] using hproj
    have hpair :
        ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
          rate rewards C_star C_h t h d = q := rfl
    have hpoint : reconstructedPairUpdate rate rewards C_star C_h control0 t h d =
        readout q := by
      simp only [reconstructedPairUpdate, q, readout]
      rw [hupdate]
    simp [pairTest, hpoint, hpair]
  have hroot :=
    ReferenceRankInstallationSourceKernelComposition.installationEvent_sourceLawNumericalKernel
      rate rewards C_star C_h control0 k t z hz pairTest hpairTest
  rcases hroot with
    ⟨L, b, v₀, valid₀, _hL, _hb, hv₀, _hfastPush, _hweights, _hslow,
      hrootCoeff, _hrecMarg, _hfastMarg, _hatoms, _hcomplement⟩
  have hvEq : v₀ = v := Option.some.inj (hv₀.symm.trans hv)
  subst v₀
  have hvalidEq : valid₀ = valid := Subsingleton.elim _ _
  subst valid₀
  calc
    _ = ReferenceRankInstallationRecorderFastSourceLaw.sourceLawTestCoefficient
        rate rewards C_star C_h t h pairTest := hcoeff
    _ = ReferenceRankInstallationSourceKernelComposition.installationRecorderFastOutputKernel
        rate t v valid pairTest := hrootCoeff
    _ = commonUpdateKernel rate rewards t v valid before B := by
      rw [commonUpdateKernel]
      change (ReferenceRankInstallationSourceKernelComposition.installationRecorderFastOutputKernel
          rate t v valid) (readout ⁻¹' B) = _
      exact (Measure.map_apply hreadout hB).symm

/-- The history/remainder law is pushed through the literal all-d observer
map, retaining the complete remainder on the original restricted source. -/
def historyRemainderCommonUpdateMap
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (q : History p × Remainder p) : History p × PairUpdate p :=
  (q.1, reconstructedPairUpdate rate rewards C_star C_h control0 t q.1 q.2)

/-- Decorate the accepted history/remainder/output triple with the literal
reconstructed whole update. -/
def historyRemainderOutputCommonUpdateMap
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (q : History p × (Remainder p × Pair p)) : History p × PairUpdate p :=
  historyRemainderCommonUpdateMap rate rewards C_star C_h control0 t (q.1, q.2.1)

/-- The actual source history paired with its actual recorder/FAST output and
whole numerical update. -/
def actualHistoryCommonUpdateMap
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) : History p × PairUpdate p :=
  (historyAt control0 k t z,
    (actualPair t z,
      ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
        rate rewards C_star C_h control0 t z))

theorem measurable_historyRemainderCommonUpdateMap
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable (historyRemainderCommonUpdateMap rate rewards C_star C_h control0 t) := by
  have hrec : Measurable (fun q : History p × Remainder p =>
      reconstructedPairUpdate rate rewards C_star C_h control0 t q.1 q.2) :=
    measurable_reconstructedPairUpdate rate rewards C_star C_h control0 t
  exact measurable_fst.prodMk hrec

theorem measurable_historyRemainderOutputCommonUpdateMap
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable (historyRemainderOutputCommonUpdateMap rate rewards C_star C_h control0 t) := by
  exact (measurable_historyRemainderCommonUpdateMap rate rewards C_star C_h control0 t).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

theorem measurable_actualHistoryCommonUpdateMap
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T) :
    Measurable (actualHistoryCommonUpdateMap rate rewards C_star C_h control0 k t) := by
  exact (ReferenceRankInstallationRecorderFoundation.measurable_history
      rate rewards C_star C_h control0 k t).prodMk
    ((ReferenceRankInstallationRecorderFastLaw.measurable_actualMarkerReservedFast
      rate rewards C_star C_h t).prodMk
      (ReferenceRankInstallationPostUpdateProposalLaw.measurable_actualInstallationNumericalUpdate
        rate rewards C_star C_h control0 t))

/-- The source pushforward and full history/remainder product agree after
forming the common pair/update observer. The equality on the restricted source
uses the all-remainder observer proof, including the source's own prefix and
current replacement. -/
theorem installationEvent_history_pairUpdate_pushforward
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)).map
        (actualHistoryCommonUpdateMap rate rewards C_star C_h control0 k t) =
      ((((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)).map
          (historyAt control0 k t)).prod
        (ReferenceLaterOptionalControlResampling.controlRemainderLaw p)).map
          (historyRemainderCommonUpdateMap rate rewards C_star C_h control0 t) := by
  let μ := (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)
  let H := historyAt control0 k t
  let R := ReferenceRankInstallationRecorderFastSourceLaw.historyRemainderMap
    rate rewards C_star C_h control0 k t
  let G := ReferenceRankInstallationSourceKernelComposition.actualHistoryRemainderOutputMap
    rate rewards C_star C_h control0 k t
  let F := historyRemainderOutputCommonUpdateMap rate rewards C_star C_h control0 t
  let Fdirect := historyRemainderCommonUpdateMap rate rewards C_star C_h control0 t
  have hμE : MeasurableSet (installEvent k t) :=
    ReferenceRankInstallationRecorderFoundation.measurableSet_installationEvent
      rate rewards C_star C_h control0 k t
  have hR : Measurable R :=
    ReferenceRankInstallationRecorderFastSourceLaw.measurable_historyRemainderMap
      rate rewards C_star C_h control0 k t
  have hG : Measurable G :=
    ReferenceRankInstallationSourceKernelComposition.measurable_actualHistoryRemainderOutputMap
      rate rewards C_star C_h control0 k t
  have hF : Measurable F := measurable_historyRemainderOutputCommonUpdateMap
    rate rewards C_star C_h control0 t
  have hFdirect : Measurable Fdirect := measurable_historyRemainderCommonUpdateMap
    rate rewards C_star C_h control0 t
  have hrootG : Measurable
      (ReferenceRankInstallationSourceKernelComposition.historyRemainderOutputMap
        rate rewards C_star C_h t) :=
    ReferenceRankInstallationSourceKernelComposition.measurable_historyRemainderOutputMap
      rate rewards C_star C_h t
  have hpoint (z : SourceInput p) (hz : z ∈ installEvent k t) :
      actualHistoryCommonUpdateMap rate rewards C_star C_h control0 k t z =
        F (G z) := by
    obtain ⟨v, _valid, hv, hall⟩ :=
      reconstructedObserver_eq_commonReadout rate rewards C_star C_h control0 k t z hz
    let d :=
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        (ReferenceSourceCurrentControlFreshness.u_t p t z)).2
    let h := H z
    let q := ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
      rate rewards C_star C_h t h d
    have hpair :=
      ReferenceRankInstallationRecorderFastSourceLaw.actualPair_eq_historyRemainder_of_installation
        rate rewards C_star C_h control0 k t z hz
    have hobs := hall d
    have hx :
        ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder t h d ∈
          installEvent k t := hobs.1
    have hrecUpdate :
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 t
            (ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder t h d) =
          updateFromPair rate rewards t v
            (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
              rate rewards C_star C_h control0 t z) q := by
      have hp := congrArg
        (fun o : ReferenceRankInstallationPostUpdateProposalLaw.Observer p rate.eta => o.2.2)
        hobs.2
      simpa [ReferenceRankInstallationPostUpdateProposalLaw.actualRankPreProposalObserver,
        h, d, q] using hp
    have hactualUpdate := actualInstallationNumericalUpdate_eq_updateFromPair
      rate rewards C_star C_h control0 k t z hz v hv
    have hqactual : actualPair t z = q := by
      simpa [q, h, d, G, R] using hpair
    have hupdateEq :
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
            rate rewards C_star C_h control0 t z =
          ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
            rate rewards C_star C_h control0 t
              (ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder t h d) := by
      rw [hactualUpdate, hrecUpdate, hqactual]
    have hpairUpdate :
        (actualPair t z,
          ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
            rate rewards C_star C_h control0 t z) =
          reconstructedPairUpdate rate rewards C_star C_h control0 t (H z) d := by
      change (actualPair t z,
          ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
            rate rewards C_star C_h control0 t z) = (q,
          ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
            rate rewards C_star C_h control0 t
              (ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder
                t (H z) d))
      exact Prod.ext hqactual hupdateEq
    change (H z, (actualPair t z,
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 t z)) =
      (H z, reconstructedPairUpdate rate rewards C_star C_h control0 t (H z) d)
    exact congrArg (fun u => (H z, u)) hpairUpdate
  calc
    _ = μ.map (fun z => F (G z)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hμE] with z hz
      exact hpoint z hz
    _ = (μ.map G).map F := by
      change μ.map (F ∘ G) = _
      exact (Measure.map_map hF hG).symm
    _ = (((((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (installEvent k t)).map H).prod
        (ReferenceLaterOptionalControlResampling.controlRemainderLaw p)).map
          (ReferenceRankInstallationSourceKernelComposition.historyRemainderOutputMap
            rate rewards C_star C_h t)).map F := by
      rw [ReferenceRankInstallationSourceKernelComposition.installationEvent_history_remainder_output_pushforward
        rate rewards C_star C_h control0 k t]
    _ = _ := by
      rw [Measure.map_map hF hrootG]
      change ((((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (installEvent k t)).map H).prod
        (ReferenceLaterOptionalControlResampling.controlRemainderLaw p)).map Fdirect = _
      rfl

/-- Arbitrary Borel history and common pair/update cylinders have the literal
history/remainder coefficient under the unnormalized restricted source law. -/
theorem installationEvent_history_pairUpdate_cylinder
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (A : Set (History p)) (B : Set (PairUpdate p))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)).map
      (actualHistoryCommonUpdateMap rate rewards C_star C_h control0 k t)) (A ×ˢ B) =
      ∫⁻ h in A, sourceLawCommonUpdateTestCoefficient
        rate rewards C_star C_h control0 t h B ∂
          (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
            (installEvent k t)).map (historyAt control0 k t)) := by
  classical
  let μ := (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)
  let ν := μ.map (historyAt control0 k t)
  let R := ReferenceLaterOptionalControlResampling.controlRemainderLaw p
  let F := historyRemainderCommonUpdateMap rate rewards C_star C_h control0 t
  have hF : Measurable F := measurable_historyRemainderCommonUpdateMap
    rate rewards C_star C_h control0 t
  have hAB : MeasurableSet (A ×ˢ B) := hA.prod hB
  have hpre : MeasurableSet (F ⁻¹' (A ×ˢ B)) := hAB.preimage hF
  let f : History p × Remainder p → ENNReal := fun q =>
    if q ∈ F ⁻¹' (A ×ˢ B) then 1 else 0
  have hf : Measurable f := Measurable.ite hpre measurable_const measurable_const
  calc
    _ = (ν.prod R) (F ⁻¹' (A ×ˢ B)) := by
      rw [installationEvent_history_pairUpdate_pushforward rate rewards C_star C_h
        control0 k t, Measure.map_apply hF hAB]
    _ = ∫⁻ q, f q ∂(ν.prod R) := by
      simpa [f, Set.indicator_apply] using (lintegral_indicator_one hpre).symm
    _ = ∫⁻ h, ∫⁻ d, f (h, d) ∂R ∂ν := lintegral_prod f hf.aemeasurable
    _ = ∫⁻ h, if h ∈ A then
          sourceLawCommonUpdateTestCoefficient rate rewards C_star C_h control0 t h B
        else 0 ∂ν := by
      apply lintegral_congr
      intro h
      by_cases ha : h ∈ A
      · simp [f, F, historyRemainderCommonUpdateMap, ha,
          sourceLawCommonUpdateTestCoefficient, R]
      · simp [f, F, historyRemainderCommonUpdateMap, ha]
    _ = ∫⁻ h in A, sourceLawCommonUpdateTestCoefficient
          rate rewards C_star C_h control0 t h B ∂ν := by
      rw [← lintegral_indicator hA]
      apply lintegral_congr
      intro h
      by_cases ha : h ∈ A <;> simp [ha]

/-- Event-test zero extension of the literal history/remainder coefficient;
no physical view or output law is selected off the installation event. -/
def commonUpdateKernelTest (control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (t : Fin p.T) (B : Set (PairUpdate p)) (z : SourceInput p) : ENNReal := by
  classical
  exact if hz : z ∈ installEvent k t then
    let v := ReferenceRankInstallationSourceKernelComposition.installationEventView
      rate rewards C_star C_h control0 k t z hz
    commonUpdateKernel rate rewards t v
      (ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
        rate rewards C_star C_h t z v
        (ReferenceRankInstallationSourceKernelComposition.installationEventView_eq
          rate rewards C_star C_h control0 k t z hz))
      (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 t z) B
  else 0

theorem measurable_commonUpdateKernelTest
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (B : Set (PairUpdate p)) (hB : MeasurableSet B) :
    Measurable (commonUpdateKernelTest rate rewards C_star C_h control0 k t B) := by
  classical
  have hE := ReferenceRankInstallationRecorderFoundation.measurableSet_installationEvent
    rate rewards C_star C_h control0 k t
  have hH := ReferenceRankInstallationRecorderFoundation.measurable_history
    rate rewards C_star C_h control0 k t
  have hcoeff := measurable_sourceLawCommonUpdateTestCoefficient
    rate rewards C_star C_h control0 t B hB
  have htest : Measurable (fun z : SourceInput p =>
      if z ∈ installEvent k t then
        sourceLawCommonUpdateTestCoefficient rate rewards C_star C_h control0 t
          (historyAt control0 k t z) B else 0) :=
    Measurable.ite hE (hcoeff.comp hH) measurable_const
  have heq : commonUpdateKernelTest rate rewards C_star C_h control0 k t B = fun z =>
      if z ∈ installEvent k t then
        sourceLawCommonUpdateTestCoefficient rate rewards C_star C_h control0 t
          (historyAt control0 k t z) B else 0 := by
    funext z
    by_cases hz : z ∈ installEvent k t
    · let v := ReferenceRankInstallationSourceKernelComposition.installationEventView
        rate rewards C_star C_h control0 k t z hz
      have hv := ReferenceRankInstallationSourceKernelComposition.installationEventView_eq
        rate rewards C_star C_h control0 k t z hz
      have hvalid := ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
        rate rewards C_star C_h t z v hv
      rw [commonUpdateKernelTest, dite_eq_left hz]
      dsimp only [v]
      rw [sourceLawCommonUpdateTestCoefficient_eq_kernel
        rate rewards C_star C_h control0 k t z hz v hvalid hv B hB]
      simp only [ite_eq_left hz]
      change (commonUpdateKernel rate rewards t v
        (ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
          rate rewards C_star C_h t z v hv)
        (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
          rate rewards C_star C_h control0 t z) B) =
        (commonUpdateKernel rate rewards t v hvalid
          (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
            rate rewards C_star C_h control0 t z) B)
      rfl
    · simp [commonUpdateKernelTest, hz]
  rw [heq]
  exact htest

/-- At every actual source point, the zero-extended coefficient is identified
with that point's own actual view and strict-past state kernel. -/
theorem commonUpdateKernelTest_eq_actualKernel
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ installEvent k t)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) (hv : viewAt t z = some v)
    (B : Set (PairUpdate p)) (_hB : MeasurableSet B) :
    commonUpdateKernelTest rate rewards C_star C_h control0 k t B z =
      commonUpdateKernel rate rewards t v valid
        (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
          rate rewards C_star C_h control0 t z) B := by
  let v₀ := ReferenceRankInstallationSourceKernelComposition.installationEventView
    rate rewards C_star C_h control0 k t z hz
  have hv₀ := ReferenceRankInstallationSourceKernelComposition.installationEventView_eq
    rate rewards C_star C_h control0 k t z hz
  have hvEq : v₀ = v := Option.some.inj (hv₀.symm.trans hv)
  subst v
  have hvalid₀ := ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
    rate rewards C_star C_h t z v₀ hv₀
  have hvalidEq : hvalid₀ = valid := Subsingleton.elim _ _
  subst hvalid₀
  simp only [commonUpdateKernelTest, dite_eq_left hz]
  rfl

/-- The original restricted-source H/(pair, whole numerical update) cylinder
is the integral of the identified correlated update kernel at each source's
own view and strict-past readout. -/
theorem installationEvent_actual_commonUpdate_cylinder
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (A : Set (History p)) (B : Set (PairUpdate p))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ installEvent k t ∧ historyAt control0 k t z ∈ A ∧
          (actualPair t z,
            ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
              rate rewards C_star C_h control0 t z) ∈ B} =
      ∫⁻ z, (historyAt control0 k t ⁻¹' A).indicator
        (commonUpdateKernelTest rate rewards C_star C_h control0 k t B) z ∂
          ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)) := by
  classical
  let μ := (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)
  let H := historyAt control0 k t
  let O := actualHistoryCommonUpdateMap rate rewards C_star C_h control0 k t
  have hO : Measurable O := measurable_actualHistoryCommonUpdateMap
    rate rewards C_star C_h control0 k t
  have hAB : MeasurableSet (A ×ˢ B) := hA.prod hB
  have hE : MeasurableSet (installEvent k t) :=
    ReferenceRankInstallationRecorderFoundation.measurableSet_installationEvent
      rate rewards C_star C_h control0 k t
  have hcoeff := measurable_sourceLawCommonUpdateTestCoefficient
    rate rewards C_star C_h control0 t B hB
  have htest : Measurable (fun h : History p => if h ∈ A then
      sourceLawCommonUpdateTestCoefficient rate rewards C_star C_h control0 t h B else 0) :=
    Measurable.ite hA hcoeff measurable_const
  calc
    _ = (μ.map O) (A ×ˢ B) := by
      have hset : {z | z ∈ installEvent k t ∧ historyAt control0 k t z ∈ A ∧
          (actualPair t z,
            ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
              rate rewards C_star C_h control0 t z) ∈ B} =
          O ⁻¹' (A ×ˢ B) ∩ installEvent k t := by
        ext z
        change (z ∈ installEvent k t ∧ H z ∈ A ∧
          (actualPair t z,
            ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
              rate rewards C_star C_h control0 t z) ∈ B) ↔
          (O z ∈ A ×ˢ B ∧ z ∈ installEvent k t)
        simp only [O, actualHistoryCommonUpdateMap, Set.mem_prod]
        exact ⟨fun ⟨he, ha, hb⟩ => ⟨⟨ha, hb⟩, he⟩,
          fun ⟨⟨ha, hb⟩, he⟩ => ⟨he, ha, hb⟩⟩
      rw [Measure.map_apply hO hAB]
      rw [Measure.restrict_apply (hAB.preimage hO), hset]
    _ = ∫⁻ h in A, sourceLawCommonUpdateTestCoefficient
          rate rewards C_star C_h control0 t h B ∂(μ.map H) :=
      installationEvent_history_pairUpdate_cylinder rate rewards C_star C_h
        control0 k t A B hA hB
    _ = ∫⁻ z, (H ⁻¹' A).indicator
          (commonUpdateKernelTest rate rewards C_star C_h control0 k t B) z ∂μ := by
      rw [← lintegral_indicator hA]
      calc
        _ = ∫⁻ z, (if H z ∈ A then
              sourceLawCommonUpdateTestCoefficient rate rewards C_star C_h control0 t
                (H z) B else 0) ∂μ := by
          change (∫⁻ h, (fun h : History p => if h ∈ A then
            sourceLawCommonUpdateTestCoefficient rate rewards C_star C_h control0 t h B
              else 0) h ∂(μ.map H)) = _
          exact lintegral_map htest
            (ReferenceRankInstallationRecorderFoundation.measurable_history
              rate rewards C_star C_h control0 k t)
        _ = ∫⁻ z, (H ⁻¹' A).indicator
              (commonUpdateKernelTest rate rewards C_star C_h control0 k t B) z ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hE] with z hz
          by_cases ha : H z ∈ A
          · let v := ReferenceRankInstallationSourceKernelComposition.installationEventView
              rate rewards C_star C_h control0 k t z hz
            have hv := ReferenceRankInstallationSourceKernelComposition.installationEventView_eq
              rate rewards C_star C_h control0 k t z hz
            have hvalid := ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
              rate rewards C_star C_h t z v hv
            have hcoeff := sourceLawCommonUpdateTestCoefficient_eq_kernel
              rate rewards C_star C_h control0 k t z hz v hvalid hv B hB
            have hkernel := commonUpdateKernelTest_eq_actualKernel
              rate rewards C_star C_h control0 k t z hz v hvalid hv B hB
            calc
              _ = (commonUpdateKernel rate rewards t v hvalid
                  (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
                    rate rewards C_star C_h control0 t z) B) := by
                rw [ite_eq_left ha, hcoeff]
              _ = commonUpdateKernelTest rate rewards C_star C_h control0 k t B z :=
                hkernel.symm
              _ = (H ⁻¹' A).indicator
                    (commonUpdateKernelTest rate rewards C_star C_h control0 k t B) z := by
                change commonUpdateKernelTest rate rewards C_star C_h control0 k t B z =
                  (if H z ∈ A then
                    commonUpdateKernelTest rate rewards C_star C_h control0 k t B z else 0)
                simp only [ite_eq_left ha]
          · simp [ha, H]

/-- Project the accepted original proposal split onto the common history,
correlated recorder/FAST pair, and whole numerical update observer. -/
theorem installationEvent_commonUpdate_proposal_pushforward
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T) :
    let μ := (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)
    μ.map (fun z =>
        (actualHistoryCommonUpdateMap rate rewards C_star C_h control0 k t z,
          ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
            (ReferenceSourceCurrentControlFreshness.u_t p t z))) =
      (μ.map (actualHistoryCommonUpdateMap rate rewards C_star C_h control0 k t)).prod
        (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate) := by
  let μ := (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)
  let H := historyAt control0 k t
  let N := ReferenceRankInstallationPostUpdateProposalLaw.originalNonProposalSource
    control0 t
  let O := ReferenceRankInstallationPostUpdateProposalLaw.actualRankPreProposalObserver
    rate rewards C_star C_h control0 t
  let G := fun z : SourceInput p => (H z, (N z, O z))
  let bit := fun z : SourceInput p =>
    ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
      (ReferenceSourceCurrentControlFreshness.u_t p t z)
  let project : History p × (SourceInput p ×
      ReferenceRankInstallationPostUpdateProposalLaw.Observer p rate.eta) →
        History p × PairUpdate p := fun q => (q.1, q.2.2.2)
  let projectBit :
      (History p × (SourceInput p ×
        ReferenceRankInstallationPostUpdateProposalLaw.Observer p rate.eta)) × Bool →
        (History p × PairUpdate p) × Bool := fun q => (project q.1, q.2)
  have hH : Measurable H :=
    ReferenceRankInstallationRecorderFoundation.measurable_history
      rate rewards C_star C_h control0 k t
  have hN : Measurable N :=
    ReferenceRankInstallationPostUpdateProposalLaw.measurable_originalNonProposalSource
      control0 t
  have hO : Measurable O :=
    ReferenceRankInstallationPostUpdateProposalLaw.measurable_actualRankPreProposalObserver
      rate rewards C_star C_h control0 t
  have hG : Measurable G := hH.prodMk (hN.prodMk hO)
  have hbit : Measurable bit :=
    (ReferenceFirstLivePostUpdateProposalLaw.measurable_physicalProposalBit rate).comp
      (ReferenceSourceCurrentControlFreshness.measurable_u_t t)
  have hGbit : Measurable (fun z => (G z, bit z)) := hG.prodMk hbit
  have hproject : Measurable project :=
    measurable_fst.prodMk (measurable_snd.comp
      (measurable_snd.comp measurable_snd))
  have hprojectBit : Measurable projectBit :=
    (hproject.comp measurable_fst).prodMk measurable_snd
  have hactual : Measurable
      (actualHistoryCommonUpdateMap rate rewards C_star C_h control0 k t) :=
    measurable_actualHistoryCommonUpdateMap rate rewards C_star C_h control0 k t
  have haccepted :=
    ReferenceRankInstallationPostUpdateProposalLaw.installationEvent_original_joint_proposal_law
      rate rewards C_star C_h control0 k t
  calc
    _ = μ.map (projectBit ∘ fun z => (G z, bit z)) := by
      rfl
    _ = (μ.map (fun z => (G z, bit z))).map projectBit :=
      (Measure.map_map hprojectBit hGbit).symm
    _ = ((μ.map G).prod
        (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate)).map projectBit := by
      rw [haccepted]
    _ = ((μ.map G).map project).prod
        (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate) := by
      change ((μ.map G).prod
          (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate)).map
            (Prod.map project id) = _
      rw [← Measure.map_prod_map (μ.map G)
        (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate)
        hproject measurable_id]
      rw [Measure.map_id]
    _ = (μ.map
        (actualHistoryCommonUpdateMap rate rewards C_star C_h control0 k t)).prod
          (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate) := by
      congr 1
      rw [Measure.map_map hproject hG]
      rfl

/-- The original source joint cylinder with the actual common pair/update and
the same independent proposal bit equals its finite correlated update-kernel
coefficient times the original Bernoulli factor. -/
theorem installationEvent_actual_commonUpdate_joint_proposal_law
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (A : Set (History p)) (B : Set (PairUpdate p)) (Dset : Set Bool)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hD : MeasurableSet Dset) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ installEvent k t ∧ historyAt control0 k t z ∈ A ∧
          (actualPair t z,
            ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
              rate rewards C_star C_h control0 t z) ∈ B ∧
          ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
            (ReferenceSourceCurrentControlFreshness.u_t p t z) ∈ Dset} =
      ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate Dset *
        (∫⁻ z, (historyAt control0 k t ⁻¹' A).indicator
          (commonUpdateKernelTest rate rewards C_star C_h control0 k t B) z ∂
            ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t))) := by
  classical
  let μ := (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)
  let H := historyAt control0 k t
  let O := actualHistoryCommonUpdateMap rate rewards C_star C_h control0 k t
  let bit := fun z : SourceInput p =>
    ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
      (ReferenceSourceCurrentControlFreshness.u_t p t z)
  let joint := fun z : SourceInput p => (O z, bit z)
  let target := (A ×ˢ B) ×ˢ Dset
  have hO : Measurable O := measurable_actualHistoryCommonUpdateMap
    rate rewards C_star C_h control0 k t
  have hbit : Measurable bit :=
    (ReferenceFirstLivePostUpdateProposalLaw.measurable_physicalProposalBit rate).comp
      (ReferenceSourceCurrentControlFreshness.measurable_u_t t)
  have hjoint : Measurable joint := hO.prodMk hbit
  have hAB : MeasurableSet (A ×ˢ B) := hA.prod hB
  have htarget : MeasurableSet target := hAB.prod hD
  have hpre : MeasurableSet (joint ⁻¹' target) := htarget.preimage hjoint
  have hE : MeasurableSet (installEvent k t) :=
    ReferenceRankInstallationRecorderFoundation.measurableSet_installationEvent
      rate rewards C_star C_h control0 k t
  have hset : {z | z ∈ installEvent k t ∧ historyAt control0 k t z ∈ A ∧
      (actualPair t z,
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 t z) ∈ B ∧ bit z ∈ Dset} =
        joint ⁻¹' target ∩ installEvent k t := by
    ext z
    change (z ∈ installEvent k t ∧ H z ∈ A ∧
      (actualPair t z,
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 t z) ∈ B ∧ bit z ∈ Dset) ↔
      (joint z ∈ target ∧ z ∈ installEvent k t)
    simp only [joint, target, O, actualHistoryCommonUpdateMap, Set.mem_prod]
    exact ⟨fun ⟨he, ha, hb, hd⟩ => ⟨⟨⟨ha, hb⟩, hd⟩, he⟩,
      fun ⟨⟨⟨ha, hb⟩, hd⟩, he⟩ => ⟨he, ha, hb, hd⟩⟩
  have hprojected :=
    installationEvent_commonUpdate_proposal_pushforward rate rewards C_star C_h
      control0 k t
  have hsetAB :
      {z | z ∈ installEvent k t ∧ historyAt control0 k t z ∈ A ∧
            (actualPair t z,
              ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
                rate rewards C_star C_h control0 t z) ∈ B} =
        O ⁻¹' (A ×ˢ B) ∩ installEvent k t := by
    ext z
    change (z ∈ installEvent k t ∧ historyAt control0 k t z ∈ A ∧
      (actualPair t z,
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 t z) ∈ B) ↔
      (O z ∈ A ×ˢ B ∧ z ∈ installEvent k t)
    simp only [O, actualHistoryCommonUpdateMap, Set.mem_prod]
    exact ⟨fun ⟨he, ha, hb⟩ => ⟨⟨ha, hb⟩, he⟩,
      fun ⟨⟨ha, hb⟩, he⟩ => ⟨he, ha, hb⟩⟩
  have hmap :
      (BootstrapPrivateRoundStreams.sourceInputLaw p)
          {z | z ∈ installEvent k t ∧ historyAt control0 k t z ∈ A ∧
            (actualPair t z,
              ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
                rate rewards C_star C_h control0 t z) ∈ B} =
        (μ.map O) (A ×ˢ B) := by
    calc
      _ = μ (O ⁻¹' (A ×ˢ B)) := by
        rw [Measure.restrict_apply (hAB.preimage hO), hsetAB]
      _ = (μ.map O) (A ×ˢ B) := (Measure.map_apply hO hAB).symm
  have hcylinder := installationEvent_actual_commonUpdate_cylinder
    rate rewards C_star C_h control0 k t A B hA hB
  calc
    _ = μ (joint ⁻¹' target) := by
      rw [hset, Measure.restrict_apply hpre]
    _ = (μ.map joint) target := (Measure.map_apply hjoint htarget).symm
    _ = ((μ.map O).prod
        (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate)) target := by
      rw [hprojected]
    _ = (μ.map O) (A ×ˢ B) *
        ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate Dset := by
      rw [Measure.prod_prod]
    _ = ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate Dset *
        (∫⁻ z, (H ⁻¹' A).indicator
          (commonUpdateKernelTest rate rewards C_star C_h control0 k t B) z ∂μ) := by
      rw [← hmap, hcylinder]
      exact mul_comm _ _

/-- The true and false joint atoms use the actual proposal hazard, without a
positive-mass assumption on the installation event or on the history cell. -/
theorem installationEvent_actual_commonUpdate_proposal_true_false
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) (t : Fin p.T)
    (A : Set (History p)) (B : Set (PairUpdate p))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ installEvent k t ∧ historyAt control0 k t z ∈ A ∧
          (actualPair t z,
            ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
              rate rewards C_star C_h control0 t z) ∈ B ∧
          ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
            (ReferenceSourceCurrentControlFreshness.u_t p t z) = true} =
      ENNReal.ofReal (4 * (p.m : ℝ) * rate.eta.val) *
        (∫⁻ z, (historyAt control0 k t ⁻¹' A).indicator
          (commonUpdateKernelTest rate rewards C_star C_h control0 k t B) z ∂
            ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t))) ∧
    BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | z ∈ installEvent k t ∧ historyAt control0 k t z ∈ A ∧
          (actualPair t z,
            ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
              rate rewards C_star C_h control0 t z) ∈ B ∧
          ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
            (ReferenceSourceCurrentControlFreshness.u_t p t z) = false} =
      ENNReal.ofReal (1 - 4 * (p.m : ℝ) * rate.eta.val) *
        (∫⁻ z, (historyAt control0 k t ⁻¹' A).indicator
          (commonUpdateKernelTest rate rewards C_star C_h control0 k t B) z ∂
            ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t))) := by
  constructor
  · simpa only [Set.mem_singleton_iff,
      ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw_true,
      FollowerCutoffScan.proposalHazard] using
      (installationEvent_actual_commonUpdate_joint_proposal_law rate rewards C_star C_h
        control0 k t A B {true} hA hB (measurableSet_singleton true))
  · simpa only [Set.mem_singleton_iff,
      ReferenceRankInstallationPostUpdateProposalLaw.proposalBitLaw_false,
      FollowerCutoffScan.proposalHazard] using
      (installationEvent_actual_commonUpdate_joint_proposal_law rate rewards C_star C_h
        control0 k t A B {false} hA hB (measurableSet_singleton false))

end Bandits.Support.ReferenceRankInstallationCommonUpdateJointLaw

end
