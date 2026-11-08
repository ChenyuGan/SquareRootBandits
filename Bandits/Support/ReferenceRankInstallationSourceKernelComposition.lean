/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceRankInstallationRecorderFastSourceLaw

/-!
# Original-source coefficient and correlated recorder/FAST kernel composition

At an actual rank installation, every replacement of the current nonassignment
remainder keeps the actual installed view and invocation event. The literal
source coefficient therefore agrees with the correlated same-slice recorder
and reserved-FAST kernel, and that identification can be used inside the
unnormalized original-source history/output cylinder.

Source evidence: ZIP4 `06_interruptions.tex:381-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceRankInstallationRecorderFoundation

namespace Bandits.Support.ReferenceRankInstallationSourceKernelComposition

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

abbrev OriginalSource (p : ConstructorDimensions.Parameters) :=
  ReferenceRankInstallationRecorderFoundation.SourceInput p
abbrev InstallationHistory (p : ConstructorDimensions.Parameters) :=
  ReferenceRankInstallationRecorderFoundation.History p
abbrev OriginalControlRemainder (p : ConstructorDimensions.Parameters) :=
  ReferenceLaterOptionalControlResampling.ControlRemainder p
abbrev RecorderFastOutput (p : ConstructorDimensions.Parameters) :=
  ReferenceRankInstallationRecorderFastSourceLaw.RecorderFastOutput p

local notation "installEvent" =>
  ReferenceRankInstallationRecorderFoundation.installationEvent rate rewards C_star C_h
local notation "viewAt" =>
  ReferenceRankInstallationRecorderFoundation.actualInstallationView rate rewards C_star C_h
local notation "historyAt" =>
  ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h
local notation "currentControl" => ReferenceSourceCurrentControlFreshness.u_t p
local notation "actualPair" =>
  ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h

attribute [local instance]
  ReferenceRankInstallationRecorderFoundation.sourceInputMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.optionMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.optionSingleton
  ReferenceRankInstallationRecorderFoundation.outcomeMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.outcomeDiscreteMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.outcomeOptionMeasurableSpace
  ReferenceRankInstallationRecorderFastLaw.reservedMarkerMeasurableSpace

local instance outputSingleton : MeasurableSingletonClass
    (Option (Option (Fin p.K)) × Option (Fin p.K)) := by
  constructor
  intro q
  have hleft : MeasurableSet ({q.1} : Set (Option (Option (Fin p.K)))) :=
    measurableSet_singleton q.1
  have hright : MeasurableSet ({q.2} : Set (Option (Fin p.K))) :=
    measurableSet_singleton q.2
  have heq : ({q} : Set (Option (Option (Fin p.K)) × Option (Fin p.K))) =
      {q.1} ×ˢ {q.2} := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_prod, Prod.ext_iff]
  rw [heq]
  exact hleft.prod hright

private theorem measurable_installationRecorderFastPair
    (t : Fin p.T) (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) :
    Measurable (ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
      rate t v valid) := by
  have hrec : Measurable
      (ReferenceRankInstallationRecorderFoundation.installationRecordingMap
        rate t v valid) := by
    unfold ReferenceRankInstallationRecorderFoundation.installationRecordingMap
    exact SnapshotRecordingKernel.measurable_recordingMap p
      (.live v.payload.assignment
        (ReferenceRankInstallationRecorderFoundation.installationSnapshot
          v.payload.assignment)) rate.eta.val rate.eta.property rate.sourceCap
      v.payload.anchor
      (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
      v.payload.anchor_pos
      (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
        v.complementWeights v.cutoff t valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
        v.complementWeights v.cutoff t valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
        v.complementWeights v.cutoff t valid) true
  exact hrec.prodMk (measurable_subtype_coe.comp
    (ReferenceRankInstallationRecorderFastLaw.measurable_reservedFastAtView
      rate t v valid))

def optionalRecorderFastLift
    (q : Option (Fin p.K) × Fin p.K) : RecorderFastOutput p :=
  (some q.1, some q.2)

private theorem measurable_optionalRecorderFastLift :
    Measurable (optionalRecorderFastLift (p := p)) := by
  have hleft : Measurable
      (some : Option (Fin p.K) → Option (Option (Fin p.K))) :=
    measurable_of_countable _
  have hright : Measurable (some : Fin p.K → Option (Fin p.K)) :=
    measurable_of_countable _
  exact hleft.comp measurable_fst |>.prodMk (hright.comp measurable_snd)

/-- The correlated same-slice joint law after forgetting only the subtype
proof on the reserved FAST arm. -/
def installationRecorderFastRawKernel (t : Fin p.T)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) : Measure (Option (Fin p.K) × Fin p.K) :=
  (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property
    rate.sourceCap v.payload.anchor
    (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
    v.payload.anchor_pos
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
      v.complementWeights v.cutoff t valid)
    v.payload.assignment
    (ReferenceRankInstallationRecorderFoundation.installationSnapshot
      v.payload.assignment)).map (fun q => (q.1, q.2.1))

/-- The output kernel retains the original outer-absence option and the
present-bottom recorder outcome. It is the lift of the *joint* recorder/FAST
pushforward, with no independence factorization. -/
def installationRecorderFastOutputKernel (t : Fin p.T)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) : Measure (RecorderFastOutput p) :=
  (installationRecorderFastRawKernel rate t v valid).map
    (optionalRecorderFastLift (p := p))

/-- The same correlated kernel retains the established recorder and FAST
marginals. The FAST measure is pushed from the fast-arm subtype by its value
map; no product or independence law is used. -/
theorem installationRecorderFastRawKernel_marginals (t : Fin p.T)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) :
    (installationRecorderFastRawKernel rate t v valid).map Prod.fst =
        (RecordedRoundMoments.recordingOutcomePMF
          (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
            rate.sourceCap v.payload.anchor v.payload.anchor_pos)).toMeasure ∧
      (installationRecorderFastRawKernel rate t v valid).map Prod.snd =
        (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property
          rate.sourceCap v.payload.anchor
          (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
            v.complementWeights)
          v.payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
            v.complementWeights v.cutoff t valid)
          (SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment)).toMeasure.map
          (fun j : CanonicalFastSampling.FastArm
            (SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment) => j.1) := by
  let W := ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights
  let live := FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val
    rate.eta.property rate.sourceCap v.payload.anchor W v.payload.anchor_pos
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
      v.complementWeights v.cutoff t valid)
    v.payload.assignment
    (ReferenceRankInstallationRecorderFoundation.installationSnapshot
      v.payload.assignment)
  let project := fun q : Option (Fin p.K) × CanonicalFastSampling.FastArm
      (SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment) => (q.1, q.2.1)
  have hproject : Measurable project :=
    measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
  have hfst := FastRewardSliceLaw.liveRecordingFastPushforward_fst
    p rate.eta.val rate.eta.property rate.sourceCap v.payload.anchor W
    v.payload.anchor_pos
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
      v.complementWeights v.cutoff t valid)
    v.payload.assignment
    (ReferenceRankInstallationRecorderFoundation.installationSnapshot
      v.payload.assignment)
  have hsnd := FastRewardSliceLaw.liveRecordingFastPushforward_snd
    p rate.eta.val rate.eta.property rate.sourceCap v.payload.anchor W
    v.payload.anchor_pos
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
      v.complementWeights v.cutoff t valid)
    v.payload.assignment
    (ReferenceRankInstallationRecorderFoundation.installationSnapshot
      v.payload.assignment)
  constructor
  · change (live.map project).map Prod.fst = _
    rw [Measure.map_map measurable_fst hproject]
    change live.map Prod.fst = _
    exact hfst
  · change (live.map project).map Prod.snd = _
    calc
      (live.map project).map Prod.snd = live.map (fun q => q.2.1) := by
        rw [Measure.map_map measurable_snd hproject]
        congr 1
      _ = (live.map Prod.snd).map
          (fun j : CanonicalFastSampling.FastArm
            (SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment) => j.1) := by
        rw [Measure.map_map measurable_subtype_coe measurable_snd]
        rfl
      _ = _ := congrArg
        (fun μ : Measure (CanonicalFastSampling.FastArm
          (SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment)) =>
          μ.map (fun j : CanonicalFastSampling.FastArm
            (SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment) => j.1)) hsnd

/-- The lifted output kernel has the recorder outcome masses and the
qGamma FAST marginal with the outer-presence option retained. -/
theorem installationRecorderFastOutputKernel_marginals (t : Fin p.T)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) :
    (installationRecorderFastOutputKernel rate t v valid).map Prod.fst =
        ((RecordedRoundMoments.recordingOutcomePMF
          (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
            rate.sourceCap v.payload.anchor v.payload.anchor_pos)).toMeasure).map
          (fun x : Option (Fin p.K) => some x) ∧
      (installationRecorderFastOutputKernel rate t v valid).map Prod.snd =
        (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property
          rate.sourceCap v.payload.anchor
          (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
            v.complementWeights)
          v.payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
            v.complementWeights v.cutoff t valid)
          (SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment)).toMeasure.map
          (fun j : CanonicalFastSampling.FastArm
            (SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment) => some j.1) := by
  let raw := installationRecorderFastRawKernel rate t v valid
  have hmarg := installationRecorderFastRawKernel_marginals rate t v valid
  have hleft : Measurable (fun x : Option (Fin p.K) => some x) :=
    measurable_of_countable _
  have hright : Measurable (fun x : Fin p.K => some x) :=
    measurable_of_countable _
  constructor
  · change (raw.map (optionalRecorderFastLift (p := p))).map Prod.fst = _
    rw [Measure.map_map measurable_fst
      (measurable_optionalRecorderFastLift (p := p))]
    change raw.map (fun q => some q.1) = _
    calc
      raw.map (fun q => some q.1) =
          (raw.map Prod.fst).map (fun x : Option (Fin p.K) => some x) := by
        rw [Measure.map_map hleft measurable_fst]
        rfl
      _ = _ := by rw [hmarg.1]
  · change (raw.map (optionalRecorderFastLift (p := p))).map Prod.snd = _
    rw [Measure.map_map measurable_snd
      (measurable_optionalRecorderFastLift (p := p))]
    change raw.map (fun q => some q.2) = _
    calc
      raw.map (fun q => some q.2) =
          (raw.map Prod.snd).map (fun x : Fin p.K => some x) := by
        rw [Measure.map_map hright measurable_snd]
        rfl
      _ = ((CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property
          rate.sourceCap v.payload.anchor
          (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
            v.complementWeights)
          v.payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
            v.complementWeights v.cutoff t valid)
          (SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment)).toMeasure.map
            (fun j : CanonicalFastSampling.FastArm
              (SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment) => j.1)).map
            (fun x : Fin p.K => some x) := congrArg
              (fun μ : Measure (Fin p.K) => μ.map (fun x => some x)) hmarg.2
      _ = _ := by
        rw [Measure.map_map hright measurable_subtype_coe]
        congr 1

/-- The same actual view and validity certificate work after replacing every
original remainder coordinate while fixing the complete assignment vector. -/
theorem actualPairFromHistoryRemainder_sameSlice_of_installation
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : OriginalSource p) (hz : z ∈ installEvent k t) :
    ∃ (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
      (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
        v.complementWeights),
      viewAt t z = some v ∧
      actualPair t z =
        (some (ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
          rate t v valid ((currentControl t z).1)).1,
         some (ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
          rate t v valid ((currentControl t z).1)).2) ∧
      ReferenceRankInstallationRecorderFoundation.actualMarker rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
            (currentControl t z)) =
        ReferenceRankInstallationRecorderFoundation.actualMarker rate rewards C_star C_h t z ∧
      ∀ d : OriginalControlRemainder p,
        let source := ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder
          t (historyAt control0 k t z) d
        let slice := (LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm
          (ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z, d.1)
        source ∈ installEvent k t ∧
        viewAt t source = some v ∧
        ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
          rate rewards C_star C_h t (historyAt control0 k t z) d =
          (some (ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
            rate t v valid slice).1,
           some (ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
            rate t v valid slice).2) := by
  obtain ⟨v, valid, hv, hactual⟩ :=
    ReferenceRankInstallationRecorderFastLaw.installationEvent_actualMarkerReservedFast
      rate rewards C_star C_h control0 k t z hz
  obtain ⟨s, v₀, valid₀, hs, hv₀, _hmarker, hmarkerAll⟩ :=
    ReferenceRankInstallationRecorderFoundation.actualMarker_all_remaining_controls
      rate rewards C_star C_h control0 k t z hz
  have hvEq : v₀ = v := Option.some.inj (hv₀.symm.trans hv)
  subst v₀
  have hsEq : s = t := hs
  subst s
  have hvalidEq : valid₀ = valid := Subsingleton.elim _ _
  subst valid₀
  have hrestore :=
    ReferenceRankInstallationRecorderFoundation.actualMarker_restore_of_installation
      rate rewards C_star C_h control0 k t z hz
  let vector := ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z
  let controlSplit := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  let sliceSplit := LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p
  let sourcePrefix := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z
  refine ⟨v, valid, hv, hactual, hrestore, ?_⟩
  intro d
  let c := controlSplit.symm (vector, d)
  let source := ReferenceRankInstallationRecorderFastSourceLaw.sourceFromHistoryRemainder
    t (historyAt control0 k t z) d
  let slice := sliceSplit.symm (vector, d.1)
  have hsplit : controlSplit c = (vector, d) := by
    dsimp only [c]
    exact controlSplit.apply_symm_apply _
  have hsource : source =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t sourcePrefix c := by
    change ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (historyAt control0 k t z).1
        (controlSplit.symm ((historyAt control0 k t z).2.2, d)) = _
    rw [show (historyAt control0 k t z).1 = sourcePrefix by rfl,
      show (historyAt control0 k t z).2.2 = vector by rfl]
  have hvector : ContinuousControlSlice.assignmentVector c.1 = vector := by
    change (controlSplit c).1 = vector
    rw [hsplit]
  have hslice : c.1 = slice := by
    have hsliceSplit : sliceSplit c.1 = (vector, d.1) := by
      apply Prod.ext
      · change (controlSplit c).1 = vector
        rw [hsplit]
      · change (controlSplit c).2.1 = d.1
        rw [hsplit]
    calc
      c.1 = sliceSplit.symm (sliceSplit c.1) :=
        (sliceSplit.symm_apply_apply c.1).symm
      _ = slice := by rw [hsliceSplit]
  have hinvariant :=
    ReferenceRankInstallationRecorderFastLaw.installationEvent_remainder_view_invariant
      rate rewards C_star C_h control0 k t z hz c hvector
  have hview : viewAt t source = some v := by
    rw [hsource]
    exact hinvariant.2.trans hv
  have hcurrent : currentControl t source = c := by
    rw [hsource]
    simp [ReferenceSourceCurrentControlFreshness.u_t,
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      ActualInitializationPhysicalStep.selectedRowIndex]
  have hmarker := hmarkerAll c hvector
  rw [← hsource] at hmarker
  have hmarkerPair :
      ReferenceRankInstallationRecorderFoundation.actualMarker rate rewards C_star C_h
        t source =
      some (ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
        rate t v valid slice).1 := by
    simpa [ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair,
      hslice] using hmarker
  have hfast :=
    ReferenceRankInstallationRecorderFastLaw.actualReservedFast_eq_of_view
      rate rewards C_star C_h t source v hview valid
  have hfastPair :
      ReferenceRankInstallationRecorderFastLaw.actualReservedFast rate rewards C_star C_h
        t source =
      some (ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
        rate t v valid slice).2 := by
    rw [hfast, hcurrent, hslice]
    rfl
  have hpair : actualPair t source =
      (some (ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
        rate t v valid slice).1,
       some (ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
        rate t v valid slice).2) := by
    change (ReferenceRankInstallationRecorderFoundation.actualMarker
        rate rewards C_star C_h t source,
      ReferenceRankInstallationRecorderFastLaw.actualReservedFast
        rate rewards C_star C_h t source) = _
    exact Prod.ext hmarkerPair hfastPair
  refine ⟨?_, hview, ?_⟩
  · change ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
      sourcePrefix c ∈ installEvent k t
    exact hinvariant.1
  · change actualPair t source = _
    exact hpair

/-- The correlated numerical kernel for the original remainder law is exactly
the pushforward of the literal reconstructed optional pair at every actual
history. -/
theorem installationEvent_sourceLawOutput_pushforward
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : OriginalSource p) (hz : z ∈ installEvent k t)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) (hv : viewAt t z = some v) :
    (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
        (fun d => ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
          rate rewards C_star C_h t (historyAt control0 k t z) d) =
      installationRecorderFastOutputKernel rate t v valid := by
  obtain ⟨v₀, valid₀, hv₀, _hactual, _hrestore, hpoint⟩ :=
    actualPairFromHistoryRemainder_sameSlice_of_installation
      rate rewards C_star C_h control0 k t z hz
  have hvEq : v₀ = v := Option.some.inj (hv₀.symm.trans hv)
  subst v₀
  have hvalidEq : valid₀ = valid := Subsingleton.elim _ _
  subst valid₀
  obtain ⟨v₁, valid₁, hv₁, _hviewFromHistory, hpush⟩ :=
    ReferenceRankInstallationRecorderFastLaw.installationEvent_actualRemainder_joint_pushforward
      rate rewards C_star C_h control0 k t z hz
  have hv₁Eq : v₁ = v := Option.some.inj (hv₁.symm.trans hv)
  subst v₁
  have hvalid₁Eq : valid₁ = valid := Subsingleton.elim _ _
  subst valid₁
  let vector := ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z
  let sliceSplit := LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p
  let pair := fun d : OriginalControlRemainder p =>
    ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair rate t v valid
      (sliceSplit.symm (vector, d.1))
  have hpair : Measurable pair :=
    (measurable_installationRecorderFastPair rate t v valid).comp
      (sliceSplit.symm.measurable.comp
        (measurable_const.prodMk (measurable_fst)))
  have hlift := measurable_optionalRecorderFastLift (p := p)
  have hpoint' (d : OriginalControlRemainder p) :
      ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
          rate rewards C_star C_h t (historyAt control0 k t z) d =
        optionalRecorderFastLift (pair d) := by
    simpa [pair, optionalRecorderFastLift, sliceSplit, vector] using (hpoint d).2.2
  calc
    _ = (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
        (fun d => optionalRecorderFastLift (pair d)) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall hpoint'
    _ = ((ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map pair).map
        optionalRecorderFastLift := by
      change (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
        (optionalRecorderFastLift ∘ pair) = _
      exact (Measure.map_map hlift hpair).symm
    _ = installationRecorderFastOutputKernel rate t v valid := by
      rw [hpush]
      rfl

/-- The whole-carrier finite-output test coefficient at an actual history is
the mass of the same correlated numerical recorder/FAST kernel. -/
theorem sourceLawTestCoefficient_eq_numericalKernel
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : OriginalSource p) (hz : z ∈ installEvent k t)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) (hv : viewAt t z = some v)
    (B : Set (RecorderFastOutput p)) (hB : MeasurableSet B) :
    ReferenceRankInstallationRecorderFastSourceLaw.sourceLawTestCoefficient
        rate rewards C_star C_h t (historyAt control0 k t z) B =
      installationRecorderFastOutputKernel rate t v valid B := by
  classical
  obtain ⟨v₀, valid₀, hv₀, _hactual, _hrestore, hpoint⟩ :=
    actualPairFromHistoryRemainder_sameSlice_of_installation
      rate rewards C_star C_h control0 k t z hz
  have hvEq : v₀ = v := Option.some.inj (hv₀.symm.trans hv)
  subst v₀
  have hvalidEq : valid₀ = valid := Subsingleton.elim _ _
  subst valid₀
  obtain ⟨v₁, valid₁, hv₁, _hviewFromHistory, hpush⟩ :=
    ReferenceRankInstallationRecorderFastLaw.installationEvent_actualRemainder_joint_pushforward
      rate rewards C_star C_h control0 k t z hz
  have hv₁Eq : v₁ = v := Option.some.inj (hv₁.symm.trans hv)
  subst v₁
  have hvalid₁Eq : valid₁ = valid := Subsingleton.elim _ _
  subst valid₁
  let vector := ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z
  let sliceSplit := LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p
  let pair := fun d : OriginalControlRemainder p =>
    ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair rate t v valid
      (sliceSplit.symm (vector, d.1))
  let g := optionalRecorderFastLift ∘ pair
  have hpair : Measurable pair :=
    (measurable_installationRecorderFastPair rate t v valid).comp
      (sliceSplit.symm.measurable.comp
        (measurable_const.prodMk measurable_fst))
  have hlift := measurable_optionalRecorderFastLift (p := p)
  have hg : Measurable g := hlift.comp hpair
  have hpre : MeasurableSet (g ⁻¹' B) := hB.preimage hg
  have hpoint' (d : OriginalControlRemainder p) :
      ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
          rate rewards C_star C_h t (historyAt control0 k t z) d = g d := by
    simpa [g, pair, optionalRecorderFastLift, sliceSplit, vector] using (hpoint d).2.2
  let f := fun d : OriginalControlRemainder p =>
    ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
      rate rewards C_star C_h t (historyAt control0 k t z) d
  have hmass : (∫⁻ d, if f d ∈ B then (1 : ENNReal) else 0 ∂
      ReferenceLaterOptionalControlResampling.controlRemainderLaw p) =
      (∫⁻ d, if g d ∈ B then (1 : ENNReal) else 0 ∂
        ReferenceLaterOptionalControlResampling.controlRemainderLaw p) := by
    apply lintegral_congr
    intro d
    simpa [f] using congrArg (fun y : RecorderFastOutput p =>
      if y ∈ B then (1 : ENNReal) else 0) (hpoint' d)
  have hmass' : (∫⁻ d, if g d ∈ B then (1 : ENNReal) else 0 ∂
      ReferenceLaterOptionalControlResampling.controlRemainderLaw p) =
      (ReferenceLaterOptionalControlResampling.controlRemainderLaw p) (g ⁻¹' B) := by
    simpa [Set.indicator_apply] using
      (lintegral_indicator_one (μ :=
        ReferenceLaterOptionalControlResampling.controlRemainderLaw p) hpre)
  have hmap : (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map g =
      ((ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map pair).map
        optionalRecorderFastLift := by
    change (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
      (optionalRecorderFastLift ∘ pair) = _
    exact (Measure.map_map hlift hpair).symm
  calc
    _ = ∫⁻ d, if f d ∈ B then (1 : ENNReal) else 0 ∂
        ReferenceLaterOptionalControlResampling.controlRemainderLaw p := by
      rfl
    _ = ∫⁻ d, if g d ∈ B then (1 : ENNReal) else 0 ∂
        ReferenceLaterOptionalControlResampling.controlRemainderLaw p := hmass
    _ = (ReferenceLaterOptionalControlResampling.controlRemainderLaw p) (g ⁻¹' B) := hmass'
    _ = ((ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map g) B := by
      rw [Measure.map_apply hg hB]
    _ = installationRecorderFastOutputKernel rate t v valid B := by
      rw [hmap, hpush]
      rfl

/-- The atom coefficient is the same numerical kernel evaluated at a
singleton output; outer absence and present-bottom remain different atoms. -/
theorem sourceLawCoefficient_eq_numericalKernel
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : OriginalSource p) (hz : z ∈ installEvent k t)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) (hv : viewAt t z = some v)
    (y : RecorderFastOutput p) :
    ReferenceRankInstallationRecorderFastSourceLaw.sourceLawCoefficient
        rate rewards C_star C_h t (historyAt control0 k t z) y =
      installationRecorderFastOutputKernel rate t v valid {y} := by
  have htest := sourceLawTestCoefficient_eq_numericalKernel
    rate rewards C_star C_h control0 k t z hz v valid hv {y} (measurableSet_singleton y)
  have hatom :
      ReferenceRankInstallationRecorderFastSourceLaw.sourceLawCoefficient
          rate rewards C_star C_h t (historyAt control0 k t z) y =
        ReferenceRankInstallationRecorderFastSourceLaw.sourceLawTestCoefficient
          rate rewards C_star C_h t (historyAt control0 k t z) {y} := by
    unfold ReferenceRankInstallationRecorderFastSourceLaw.sourceLawCoefficient
      ReferenceRankInstallationRecorderFastSourceLaw.sourceLawTestCoefficient
    apply lintegral_congr
    intro d
    simp only [Set.mem_singleton_iff]
  exact hatom.trans htest

theorem installationEventView_isSome
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : OriginalSource p) (hz : z ∈ installEvent k t) :
    (viewAt t z).isSome = true := by
  obtain ⟨v, _valid, hv, _⟩ :=
    ReferenceRankInstallationRecorderFastLaw.installationEvent_actualMarkerReservedFast
      rate rewards C_star C_h control0 k t z hz
  rw [hv]
  rfl

/-- The canonical actual view, extracted only on the actual installation
event. No replacement view is supplied or selected. -/
def installationEventView (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : OriginalSource p) (hz : z ∈ installEvent k t) :
    ReferenceDownReception.ChoiceTimeView p rate.eta :=
  (viewAt t z).get (installationEventView_isSome rate rewards C_star C_h
    control0 k t z hz)

theorem installationEventView_eq
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : OriginalSource p) (hz : z ∈ installEvent k t) :
    viewAt t z = some (installationEventView rate rewards C_star C_h
      control0 k t z hz) :=
  (Option.coe_get (installationEventView_isSome rate rewards C_star C_h
    control0 k t z hz)).symm

/-- The numerical test readout is defined from the actual source's own view
on the event. It is extended by zero only outside the restricted source
measure used by the cylinder below. -/
def installationEventNumericalKernelTest (control0 : TimeControl p) (k : ℕ)
    (t : Fin p.T) (B : Set (RecorderFastOutput p)) (z : OriginalSource p) : ENNReal := by
  classical
  exact if hz : z ∈ installEvent k t then
    let v := installationEventView rate rewards C_star C_h control0 k t z hz
    installationRecorderFastOutputKernel rate t v
      (ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
        rate rewards C_star C_h t z v
        (installationEventView_eq rate rewards C_star C_h control0 k t z hz)) B
  else 0

theorem installationEventNumericalKernelTest_eq_sourceCoefficient
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : OriginalSource p) (hz : z ∈ installEvent k t)
    (B : Set (RecorderFastOutput p)) (hB : MeasurableSet B) :
    installationEventNumericalKernelTest rate rewards C_star C_h control0 k t B z =
      ReferenceRankInstallationRecorderFastSourceLaw.sourceLawTestCoefficient
        rate rewards C_star C_h t (historyAt control0 k t z) B := by
  classical
  let v := installationEventView rate rewards C_star C_h control0 k t z hz
  have hv := installationEventView_eq rate rewards C_star C_h control0 k t z hz
  unfold installationEventNumericalKernelTest
  rw [dite_eq_left hz]
  change installationRecorderFastOutputKernel rate t v
      (ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
        rate rewards C_star C_h t z v hv) B = _
  exact (sourceLawTestCoefficient_eq_numericalKernel rate rewards C_star C_h
    control0 k t z hz v
    (ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
      rate rewards C_star C_h t z v hv) hv B hB).symm

theorem measurable_installationEventNumericalKernelTest
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (B : Set (RecorderFastOutput p)) (hB : MeasurableSet B) :
    Measurable (fun z : OriginalSource p =>
      installationEventNumericalKernelTest rate rewards C_star C_h control0 k t B z) := by
  classical
  let historyCoefficient := fun z : OriginalSource p =>
    ReferenceRankInstallationRecorderFastSourceLaw.sourceLawTestCoefficient
      rate rewards C_star C_h t (historyAt control0 k t z) B
  have hhistoryCoefficient : Measurable historyCoefficient :=
    (ReferenceRankInstallationRecorderFastSourceLaw.measurable_sourceLawTestCoefficient
      rate rewards C_star C_h t B hB).comp
      (ReferenceRankInstallationRecorderFoundation.measurable_history
        rate rewards C_star C_h control0 k t)
  have hE : MeasurableSet (installEvent k t) :=
    ReferenceRankInstallationRecorderFoundation.measurableSet_installationEvent
      rate rewards C_star C_h control0 k t
  have heq :
      (fun z : OriginalSource p =>
        installationEventNumericalKernelTest rate rewards C_star C_h control0 k t B z) =
      fun z => if z ∈ installEvent k t then historyCoefficient z else 0 := by
    funext z
    by_cases hz : z ∈ installEvent k t
    · rw [installationEventNumericalKernelTest_eq_sourceCoefficient
        rate rewards C_star C_h control0 k t z hz B hB]
      simp [historyCoefficient, hz]
    · simp [installationEventNumericalKernelTest, historyCoefficient, hz]
  rw [heq]
  exact Measurable.ite hE hhistoryCoefficient measurable_const

/-- The literal original-source observer cylinder with its history coefficient
replaced, inside the same finite unnormalized restriction, by the identified
correlated numerical kernel at the actual source view. -/
theorem installationEvent_history_output_numericalKernel_cylinder
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (A : Set (InstallationHistory p)) (B : Set (RecorderFastOutput p))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)).map
      (ReferenceRankInstallationRecorderFastSourceLaw.historyPairMap
        rate rewards C_star C_h control0 k t)) (A ×ˢ B) =
      ∫⁻ z, (historyAt control0 k t ⁻¹' A).indicator
        (installationEventNumericalKernelTest rate rewards C_star C_h control0 k t B) z ∂
          ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)) := by
  classical
  let μ := (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)
  let H := historyAt control0 k t
  let ν := μ.map H
  let coefficient := fun h : InstallationHistory p =>
    ReferenceRankInstallationRecorderFastSourceLaw.sourceLawTestCoefficient
      rate rewards C_star C_h t h B
  have hH : Measurable H :=
    ReferenceRankInstallationRecorderFoundation.measurable_history
      rate rewards C_star C_h control0 k t
  have hcoeff : Measurable coefficient :=
    ReferenceRankInstallationRecorderFastSourceLaw.measurable_sourceLawTestCoefficient
      rate rewards C_star C_h t B hB
  have htest : Measurable (fun h : InstallationHistory p =>
      if h ∈ A then coefficient h else 0) := Measurable.ite hA hcoeff measurable_const
  have hE : MeasurableSet (installEvent k t) :=
    ReferenceRankInstallationRecorderFoundation.measurableSet_installationEvent
      rate rewards C_star C_h control0 k t
  calc
    _ = ∫⁻ h in A,
        ReferenceRankInstallationRecorderFastSourceLaw.sourceLawTestCoefficient
          rate rewards C_star C_h t h B ∂ν := by
      simpa [μ, ν, H] using
        (ReferenceRankInstallationRecorderFastSourceLaw.installationEvent_history_output_cylinder
          rate rewards C_star C_h control0 k t A B hA hB)
    _ = ∫⁻ h, if h ∈ A then coefficient h else 0 ∂ν := by
      rw [← lintegral_indicator hA]
      apply lintegral_congr
      intro h
      by_cases ha : h ∈ A <;> simp [coefficient, ha]
    _ = ∫⁻ z, if H z ∈ A then coefficient (H z) else 0 ∂μ := by
      change (∫⁻ h, (fun h : InstallationHistory p =>
        if h ∈ A then coefficient h else 0) h ∂(μ.map H)) = _
      exact lintegral_map htest hH
    _ = ∫⁻ z, (H ⁻¹' A).indicator
          (installationEventNumericalKernelTest rate rewards C_star C_h control0 k t B) z ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hE] with z hz
      by_cases ha : H z ∈ A
      · rw [Set.indicator_of_mem (show z ∈ H ⁻¹' A from ha)]
        rw [installationEventNumericalKernelTest_eq_sourceCoefficient
          rate rewards C_star C_h control0 k t z hz B hB]
        simp [coefficient, H, ha]
      · rw [Set.indicator_of_notMem (show z ∉ H ⁻¹' A from ha)]
        simp [ha]

/-- Push forward the whole original control remainder, including its affine
sample family, together with the history and literal output pair. -/
def historyRemainderOutputMap (t : Fin p.T)
    (q : InstallationHistory p × OriginalControlRemainder p) :
    InstallationHistory p × (OriginalControlRemainder p × RecorderFastOutput p) :=
  (q.1, (q.2,
    ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
      rate rewards C_star C_h t q.1 q.2))

theorem measurable_historyRemainderOutputMap (t : Fin p.T) :
    Measurable (historyRemainderOutputMap rate rewards C_star C_h t) :=
  measurable_fst.prodMk (measurable_snd.prodMk
    (ReferenceRankInstallationRecorderFastSourceLaw.measurable_actualPairFromHistoryRemainder
      rate rewards C_star C_h t))

def actualHistoryRemainderOutputMap (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : OriginalSource p) :
    InstallationHistory p × (OriginalControlRemainder p × RecorderFastOutput p) := by
  let q := ReferenceRankInstallationRecorderFastSourceLaw.historyRemainderMap
    rate rewards C_star C_h control0 k t z
  exact (q.1, (q.2, actualPair t z))

theorem measurable_actualHistoryRemainderOutputMap (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) :
    Measurable (actualHistoryRemainderOutputMap rate rewards C_star C_h control0 k t) := by
  have hq := ReferenceRankInstallationRecorderFastSourceLaw.measurable_historyRemainderMap
    rate rewards C_star C_h control0 k t
  have hpair := ReferenceRankInstallationRecorderFastLaw.measurable_actualMarkerReservedFast
    rate rewards C_star C_h t
  exact (measurable_fst.comp hq).prodMk
    ((measurable_snd.comp hq).prodMk hpair)

/-- The original restricted source law is the full history/remainder product
followed by the literal reconstructed output map. -/
theorem installationEvent_history_remainder_output_pushforward
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)).map
        (actualHistoryRemainderOutputMap rate rewards C_star C_h control0 k t) =
      ((((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)).map
          (historyAt control0 k t)).prod
        (ReferenceLaterOptionalControlResampling.controlRemainderLaw p)).map
          (historyRemainderOutputMap rate rewards C_star C_h t) := by
  let μ := (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)
  let H := historyAt control0 k t
  let R := ReferenceRankInstallationRecorderFastSourceLaw.historyRemainderMap
    rate rewards C_star C_h control0 k t
  let G := historyRemainderOutputMap rate rewards C_star C_h t
  have hμE : MeasurableSet (installEvent k t) :=
    ReferenceRankInstallationRecorderFoundation.measurableSet_installationEvent
      rate rewards C_star C_h control0 k t
  have hR : Measurable R :=
    ReferenceRankInstallationRecorderFastSourceLaw.measurable_historyRemainderMap
      rate rewards C_star C_h control0 k t
  have hG : Measurable G := measurable_historyRemainderOutputMap rate rewards C_star C_h t
  calc
    _ = μ.map (fun z => G (R z)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hμE] with z hz
      have hp :=
        ReferenceRankInstallationRecorderFastSourceLaw.actualPair_eq_historyRemainder_of_installation
          rate rewards C_star C_h control0 k t z hz
      change ((R z).1, ((R z).2, actualPair t z)) =
        ((R z).1, ((R z).2,
          ReferenceRankInstallationRecorderFastSourceLaw.actualPairFromHistoryRemainder
            rate rewards C_star C_h t (R z).1 (R z).2))
      exact congrArg (fun y => ((R z).1, ((R z).2, y))) hp
    _ = (μ.map R).map G := by
      change μ.map (G ∘ R) = _
      exact (Measure.map_map hG hR).symm
    _ = _ := by
      rw [ReferenceRankInstallationRecorderFastSourceLaw.installationEvent_history_remainder_product
        rate rewards C_star C_h control0 k t]

/-- Arbitrary Borel tests on the full history/remainder/output triple retain
the complete original remainder, including every affine coordinate. -/
theorem installationEvent_history_remainder_output_test
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (C : Set (InstallationHistory p × (OriginalControlRemainder p × RecorderFastOutput p)))
    (_hC : MeasurableSet C) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)).map
        (actualHistoryRemainderOutputMap rate rewards C_star C_h control0 k t) C =
      ((((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)).map
          (historyAt control0 k t)).prod
        (ReferenceLaterOptionalControlResampling.controlRemainderLaw p)).map
          (historyRemainderOutputMap rate rewards C_star C_h t) C :=
  congrArg (fun μ : Measure _ => μ C)
    (installationEvent_history_remainder_output_pushforward
      rate rewards C_star C_h control0 k t)

/-- Retain the original prefix replay, actual record, and actual view alongside
the kernel identification. The numerical weights are identified only on the
FAST complement; the whole-arm source extension still fills slow arms by the
anchor. -/
theorem installationEvent_sourceLawNumericalKernel
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : OriginalSource p) (hz : z ∈ installEvent k t)
    (B : Set (RecorderFastOutput p)) (hB : MeasurableSet B) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length)
      (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
      (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
        v.complementWeights),
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h p.T z = some L ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val] ∧
      viewAt t z = some v ∧
      (ContinuousControlSlice.sliceLaw p.m p.K).map
        (ReferenceRankInstallationRecorderFastLaw.reservedFastAtView rate t v valid) =
        (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property
          rate.sourceCap v.payload.anchor
          (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
            v.complementWeights)
          v.payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
            v.complementWeights v.cutoff t valid) v.payload.slowSet).toMeasure ∧
      (∀ j : CanonicalFastSampling.FastArm v.payload.slowSet,
        ReferenceFirstWindowNumericalStream.sourceWeights v.payload
          v.complementWeights j.1 =
          AssignmentScoreReconstruction.sourceWeightBase p ^
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
              j.1 b.val).1) ∧
      (∀ i, i ∈ v.payload.slowSet.1 →
        ReferenceFirstWindowNumericalStream.sourceWeights v.payload
          v.complementWeights i = v.payload.anchor i) ∧
      ReferenceRankInstallationRecorderFastSourceLaw.sourceLawTestCoefficient
        rate rewards C_star C_h t (historyAt control0 k t z) B =
          installationRecorderFastOutputKernel rate t v valid B ∧
      (installationRecorderFastOutputKernel rate t v valid).map Prod.fst =
        ((RecordedRoundMoments.recordingOutcomePMF
          (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
            rate.sourceCap v.payload.anchor v.payload.anchor_pos)).toMeasure).map
          (fun x : Option (Fin p.K) => some x) ∧
      (installationRecorderFastOutputKernel rate t v valid).map Prod.snd =
        (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property
          rate.sourceCap v.payload.anchor
          (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
            v.complementWeights)
          v.payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
            v.complementWeights v.cutoff t valid)
          (SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment)).toMeasure.map
          (fun j : CanonicalFastSampling.FastArm
            (SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment) => some j.1) ∧
      (∀ y : RecorderFastOutput p,
        ReferenceRankInstallationRecorderFastSourceLaw.sourceLawCoefficient
          rate rewards C_star C_h t (historyAt control0 k t z) y =
            installationRecorderFastOutputKernel rate t v valid {y}) ∧
      (∃ hcompweights : ∀ j : CanonicalFastSampling.FastArm v.payload.slowSet,
        v.complementWeights j =
          AssignmentScoreReconstruction.sourceWeightBase p ^
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
              j.1 b.val).1,
        ∀ j : CanonicalFastSampling.FastArm v.payload.slowSet,
          CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property
              valid.learning_rate_le_source_cap v.payload.anchor
              (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
                v.complementWeights)
              v.payload.anchor_pos
              (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
                v.complementWeights v.cutoff t valid)
              (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
                v.complementWeights v.cutoff t valid)
              (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
                v.complementWeights v.cutoff t valid) v.payload.slowSet j =
            FastComplementLocality.localFastLaw p rate.eta.val rate.eta.property
              valid.learning_rate_le_source_cap v.payload.anchor v.payload.slowSet
              (fun j => AssignmentScoreReconstruction.sourceWeightBase p ^
                (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
                  j.1 b.val).1)
              v.payload.anchor_pos
              (fun j => by rw [← hcompweights j]; exact valid.current_weight_pos j)
              (fun j => by rw [← hcompweights j]; exact valid.anchor_le_current j)
              (fun j => by rw [← hcompweights j]; exact valid.current_le_twice_anchor j) j) := by
  obtain ⟨L, b, v, valid, hL, hb, hv, hpush, hweights⟩ :=
    ReferenceRankInstallationRecorderFastLaw.installationEvent_originalNumericalFastMarginal
      rate rewards C_star C_h control0 k t z hz
  have hcoeff := sourceLawTestCoefficient_eq_numericalKernel
    rate rewards C_star C_h control0 k t z hz v valid hv B hB
  have hmarg := installationRecorderFastOutputKernel_marginals rate t v valid
  have hatom (y : RecorderFastOutput p) := sourceLawCoefficient_eq_numericalKernel
    rate rewards C_star C_h control0 k t z hz v valid hv y
  have hslow (i : Fin p.K) (hi : i ∈ v.payload.slowSet.1) :
      ReferenceFirstWindowNumericalStream.sourceWeights v.payload
        v.complementWeights i = v.payload.anchor i := by
    simp [ReferenceFirstWindowNumericalStream.sourceWeights, hi]
  have hcompweights (j : CanonicalFastSampling.FastArm v.payload.slowSet) :
      v.complementWeights j =
        AssignmentScoreReconstruction.sourceWeightBase p ^
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
            j.1 b.val).1 := by
    have hj : j.1 ∉ v.payload.slowSet.1 := (Finset.mem_sdiff.mp j.2).2
    have hrestrict : ReferenceFirstWindowNumericalStream.sourceWeights v.payload
        v.complementWeights j.1 = v.complementWeights j := by
      simp [ReferenceFirstWindowNumericalStream.sourceWeights, hj]
    calc
      v.complementWeights j =
          ReferenceFirstWindowNumericalStream.sourceWeights v.payload
            v.complementWeights j.1 := hrestrict.symm
      _ = AssignmentScoreReconstruction.sourceWeightBase p ^
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
            j.1 b.val).1 := hweights j
  refine ⟨L, b, v, valid, hL, hb, hv, hpush, hweights, hslow, hcoeff,
    hmarg.1, hmarg.2, hatom, hcompweights, ?_⟩
  intro j
  let W := ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights
  let numerical := fun j : CanonicalFastSampling.FastArm v.payload.slowSet =>
    AssignmentScoreReconstruction.sourceWeightBase p ^
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L j.1 b.val).1
  have hW : (fun j : CanonicalFastSampling.FastArm v.payload.slowSet => W j.1) =
      numerical := by
    funext j
    calc
      W j.1 = v.complementWeights j := by
        have hj : j.1 ∉ v.payload.slowSet.1 := (Finset.mem_sdiff.mp j.2).2
        simp [W, ReferenceFirstWindowNumericalStream.sourceWeights, hj]
      _ = numerical j := by rw [hcompweights j]
  have hnumPos (j : CanonicalFastSampling.FastArm v.payload.slowSet) :
      0 < numerical j := by
    dsimp [numerical]
    rw [← hcompweights j]
    exact valid.current_weight_pos j
  have hnumLower (j : CanonicalFastSampling.FastArm v.payload.slowSet) :
      v.payload.anchor j.1 ≤ numerical j := by
    dsimp [numerical]
    rw [← hcompweights j]
    exact valid.anchor_le_current j
  have hnumUpper (j : CanonicalFastSampling.FastArm v.payload.slowSet) :
      numerical j ≤ 2 * v.payload.anchor j.1 := by
    dsimp [numerical]
    rw [← hcompweights j]
    exact valid.current_le_twice_anchor j
  have hq := FastComplementLocality.localFastLaw_eq_qGamma p
    valid.learning_rate_pos valid.learning_rate_le_source_cap
    v.payload.anchor W v.payload.anchor_pos
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
      v.complementWeights v.cutoff t valid) v.payload.slowSet j
  calc
    CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property
        valid.learning_rate_le_source_cap v.payload.anchor W
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid) v.payload.slowSet j =
      FastComplementLocality.localFastLaw p rate.eta.val rate.eta.property
        valid.learning_rate_le_source_cap v.payload.anchor v.payload.slowSet
        (fun j => W j.1) v.payload.anchor_pos
        (fun j => ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid j.1)
        (fun j => ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid j.1)
        (fun j => ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid j.1) j := hq.symm
    _ = FastComplementLocality.localFastLaw p rate.eta.val rate.eta.property
        valid.learning_rate_le_source_cap v.payload.anchor v.payload.slowSet
        numerical v.payload.anchor_pos
        hnumPos hnumLower hnumUpper j := by
      unfold FastComplementLocality.localFastLaw
        FastComplementLocality.localConditionalFastMass
        FastComplementLocality.localFastCandidateMass
        FastComplementLocality.localFastNormalizer
      rw [hW]

end Bandits.Support.ReferenceRankInstallationSourceKernelComposition

end
