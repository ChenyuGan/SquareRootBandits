/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveRecordingReadoutMeasurability
public import Bandits.Support.ReferenceFirstLiveRecordingBranchMeasurability

/-!
# Original-source continuing first-live recording cylinders

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:376-408`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

The measures are inherited, unnormalized restrictions of the original source.
The continuing branch supplies every input to the physical recording law.
The split retains every original private coordinate, including J, and every
other row and time. This is an unstopped physical cylinder, not a conditional
law for the authentic history or a manuscript closure assertion.

The next consumer is original-source saved first and square moment integration
using `ReferenceContinuingSavedIncrementMoments` and the admitted joint saved
readouts. Strict-past overflow restrictions and authentic source-history
conditional laws remain separate obligations.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows

namespace Bandits.Support.ReferenceFirstLiveRecordingSourceCylinder

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "X" => ReferenceFirstLiveRecordingReadoutMeasurability.SourceX rate rewards C_star C_h q t s hs control0
local notation "Xplus" => ReferenceFirstLiveRecordingReadoutMeasurability.XPlus rate rewards C_star C_h q t s hs
  control0
local notation "Bplus" => ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch rate rewards C_star C_h q t
  s hs control0
local notation "μC" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h q t s hs
  control0
local notation "ctrlLaw" => timeControlLaw p

/-- The original selected-row/elapsed index. The finite bound follows from hs. -/
def stratumIndex : ReferenceTotalSourcePairCoupling.StratumIndex t :=
  (q, ⟨s, Nat.lt_succ_of_le hs⟩)

local notation "i0" => stratumIndex q t s hs
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t i0
local notation "μZ" => ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t i0

/-- The original source's retained point, with no operational extension. -/
def sourceRetained (z : Z) : X :=
  ReferenceTotalSourceDisintegration.sourceRetainedInput rate rewards C_star C_h t control0 i0 z

/-- The whole original current control, rather than a fresh draw. -/
def originalControl (z : Z) : TimeControl p := (z.val.1.2 q).2 t

/-- The literal continuing event on the original source stratum. -/
abbrev SourcePlus := {z : Z // Bplus (sourceRetained rate rewards C_star C_h q t s hs control0 z)}

local notation "Zplus" => SourcePlus rate rewards C_star C_h q t s hs control0

/-- Inherited continuing-branch remainder measure. It is not normalized. -/
def branchRemainderMeasure : Measure Xplus := (μC).comap Subtype.val

/-- Inherited continuing-branch original-source measure. It is not normalized. -/
def branchSourceMeasure : Measure Zplus := (μZ).comap Subtype.val

local notation "μCplus" => branchRemainderMeasure rate rewards C_star C_h q t s hs control0
local notation "μZplus" => branchSourceMeasure rate rewards C_star C_h q t s hs control0

instance branchRemainderMeasure_finite : IsFiniteMeasure μCplus := by
  unfold branchRemainderMeasure
  infer_instance

instance branchSourceMeasure_finite : IsFiniteMeasure μZplus := by
  unfold branchSourceMeasure
  infer_instance

theorem measurable_sourceRetained :
    Measurable (sourceRetained rate rewards C_star C_h q t s hs control0) :=
  ReferenceTotalSourceDisintegration.measurable_sourceRetainedInput rate rewards C_star C_h t control0 i0

theorem measurable_originalControl :
    Measurable (originalControl rate rewards C_star C_h q t s hs) :=
  measurable_fst.comp ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).measurable.comp
    measurable_subtype_coe)

theorem measurableSet_sourceBranch :
    MeasurableSet {z : Z | Bplus (sourceRetained rate rewards C_star C_h q t s hs control0 z)} :=
  (ReferenceFirstLiveRecordingBranchMeasurability.measurableSet_continuingRecordingBranch rate rewards C_star C_h q t s
    hs control0).preimage
    (measurable_sourceRetained rate rewards C_star C_h q t s hs control0)

/-- The canonical varying rates of the actual selected baseline payload. -/
def markerRate (x : Xplus) (j : Fin p.K) : ℝ :=
  CanonicalRecordingRates.xi p rate.eta.val (ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload
    x).anchor j

theorem measurable_markerRate (j : Fin p.K) :
    Measurable (fun x : Xplus => markerRate rate rewards C_star C_h q t s hs control0 x j) := by
  have h := (measurable_pi_apply j).comp
    (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_selectedBaselineInputRate (rate := rate) (rewards :=
      rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0))
  convert h using 1
  funext x
  exact ((ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload x).rate_eq_canonical j).symm

/-- Whole-current-control atom masses, with every physical-law input produced
from the computed branch and its unchanged actual seed. -/
theorem currentPhysicalMarker_masses (x : Xplus) :
    (∀ j : Fin p.K, ctrlLaw {u | ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker (x, u) = some j}
      =
      ENNReal.ofReal (markerRate rate rewards C_star C_h q t s hs control0 x j)) ∧
    ctrlLaw {u | ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker (x, u) = none} =
      ENNReal.ofReal (1 - ∑ j : Fin p.K,
        markerRate rate rewards C_star C_h q t s hs control0 x j) := by
  obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord,
      henabled, _, _, _, hfirst, hseed, _, _, _, _, _, hunoccupied, _,
      hvalid, hpairwise, htime, _, _⟩ :=
    ReferenceFirstLiveRecordingSourceBranch.actual_continuing_recording_inputs rate rewards C_star C_h q t s hs control0
      x.val x.property
  have hpayload := ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload_eq_of_continuing x
    r owned base d hsStart c arm hcoord
  have hlaw := ReferenceContinuingRecordingFastLaw.actual_continuing_live_joint_law
    (ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitial x.val)
      (ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceSplit x.val).1.2 q rewards s
    (t.val - s) (ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceCurrentSpan hs)
      (ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitialMode x.val)
    (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed rate rewards C_star C_h q t s hs control0
      x.val).followers
    (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed rate rewards C_star C_h q t s hs control0 x.val).memory
    hfirst hseed hunoccupied hvalid hpairwise htime
    r owned base d hsStart c arm hcoord states memories ho henabled
  rcases hlaw with ⟨hpair, _, _, _, _, hsome, hnone, _, _⟩
  rw [Measure.map_map measurable_fst hpair] at hsome hnone
  have hmarker : (fun u : TimeControl p => ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker (x, u))
    =
      ReferenceContinuingRecordingFastPair.candidatePhysicalMarker
        (ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitial x.val)
        (ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceSplit x.val).1.2 q rewards s (t.val - s)
        (ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceCurrentSpan hs)
          (ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitialMode x.val)
        r.payload true := by
    funext u
    unfold ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker
    rw [hpayload, ReferenceFirstLiveRecordingReadoutMeasurability.sourcePhysicalMarker_eq_candidatePhysicalMarker]
    rfl
  have hmeas : Measurable (fun u : TimeControl p =>
    ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker (x, u)) :=
    ReferenceFirstLiveRecordingReadoutMeasurability.measurable_currentPhysicalMarker.comp (measurable_const.prodMk
      measurable_id)
  simp only [Function.comp_def,
    ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair] at hsome hnone
  constructor
  · intro j
    have h := hsome j
    rw [← hmarker, Measure.map_apply hmeas (measurableSet_singleton _)] at h
    simpa only [markerRate, hpayload, Set.preimage, Set.mem_singleton_iff] using h
  · rw [← hmarker, Measure.map_apply hmeas (measurableSet_singleton _)] at hnone
    simpa only [markerRate, hpayload, Set.preimage, Set.mem_singleton_iff] using hnone

/-- The numerical source arm uses the SAME actual continuing selection,
pending set, prepared statuses and complement weights. No numerical state or
law is an input; all witnesses are produced from the branch. -/
theorem currentPhysicalMarker_eq_sourceArm (x : Xplus) :
    let input := ReferenceFirstLiveRecordingReadoutMeasurability.sourceCurrentInput x.val
    ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
      ∃ r owned base d hsStart c arm,
      (ReferenceActivePhysicalStep.prepare input).coordinator =
        .live r owned base (.continuingChosen d hsStart c arm) ∧
      (∀ i, ((ReferenceActivePhysicalStep.prepare input).followers.followers i).configuration =
        .ordinary (states i) (memories i)) ∧
      ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload x = r.payload ∧
      (∀ u : TimeControl p, ∃ c_u arm_u,
        (ReferenceActivePhysicalStep.prepare
          (ReferenceFirstLiveRecordingReadoutMeasurability.sourceInputAtControl x.val u)).coordinator =
          .live r owned base (.continuingChosen d hsStart c_u arm_u)) ∧
      (∀ u : TimeControl p,
        PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.dataSlot →
        ∀ i, ((ReferenceActivePhysicalStep.prepare
          (ReferenceFirstLiveRecordingReadoutMeasurability.sourceInputAtControl x.val u)).followers.followers
            i).configuration =
            .ordinary (states i) (memories i)) ∧
      ∀ u : TimeControl p,
        ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker (x, u) =
          ReferenceFirstWindowNumericalStream.sourceArm
            (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl x.val u)
            r.payload d.startResult.pending states
            (ReferenceActivePhysicalStep.liveRegistersAt r input.time).complementWeights
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            arm.choiceInputsValid := by
  intro input
  obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord,
      henabled, _, hcontrols, hdata, hfirst, hseed, _, _, _, _, _, hunoccupied, _,
      hvalid, hpairwise, htime, _, _⟩ :=
    ReferenceFirstLiveRecordingSourceBranch.actual_continuing_recording_inputs
      rate rewards C_star C_h q t s hs control0 x.val x.property
  have hpayload := ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload_eq_of_continuing x
    r owned base d hsStart c arm hcoord
  have hpoint := ReferenceContinuingRecordingFastPair.prefix_physical_fast_pair_eq
    (ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitial x.val)
    (ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceSplit x.val).1.2 q rewards s
    (t.val - s) (ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceCurrentSpan hs)
    (ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitialMode x.val)
    (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
      rate rewards C_star C_h q t s hs control0 x.val).followers
    (ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
      rate rewards C_star C_h q t s hs control0 x.val).memory
    hfirst hseed hunoccupied hvalid hpairwise htime
    r owned base d hsStart c arm hcoord states memories ho henabled
  refine ⟨states, memories, r, owned, base, d, hsStart, c, arm,
    hcoord, ho, hpayload, hcontrols, hdata, ?_⟩
  intro u
  have hmarker := congrArg Prod.fst (hpoint u)
  have hslice :
      ((ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl x.val u).input.row.2
        (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl x.val u).input.time).1 = u.1 := by
    change ((ReferenceContinuingLiveSlicePreparation.inputAtControl input u).row.2
      (ReferenceContinuingLiveSlicePreparation.inputAtControl input u).time).1 = u.1
    rw [ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
      ReferenceContinuingLiveSlicePreparation.inputAtControl_time,
      ReferenceContinuingLiveSlicePreparation.rowAtControl_time]
  unfold ReferenceFirstWindowNumericalStream.sourceArm
  rw [hslice]
  unfold ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker
  rw [hpayload,
    ReferenceFirstLiveRecordingReadoutMeasurability.sourcePhysicalMarker_eq_candidatePhysicalMarker]
  exact hmarker

/-- A recorded arm comes from the actual current selection, action and true
grid feedback, including an unoccupied follower's saved-record path. -/
theorem currentPhysicalMarker_some_actual_feedback
    (x : Xplus) (u : TimeControl p) (j : Fin p.K)
    (hj : ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker (x, u) = some j) :
    let record := ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl x.val u
    let source := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
        ((record.input.row.2 record.input.time).1))
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected ∧
      selected.view.payload = ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload x ∧
      PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.dataSlot ∧
      record.output.preparation.arms.actions source = j ∧
      record.output.preparation.feedback.feedback source = rewards record.input.time j ∧
      (record.output.preparation.feedback.observations source).val.val =
        ((rewards record.input.time j).val : ℝ) / (D p : ℝ) := by
  intro record source
  obtain ⟨states, memories, r, owned, base, d, hsStart, c, arm, hcoord, _, hmarkers⟩ :=
    ReferenceFirstLiveRecordingSourceBranch.actual_continuing_source_marker_eq
      rate rewards C_star C_h q t s hs control0 x.val x.property
  have hpayload := ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload_eq_of_continuing x
    r owned base d hsStart c arm hcoord
  unfold ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker at hj
  rw [hpayload,
    ReferenceFirstLiveRecordingReadoutMeasurability.sourcePhysicalMarker_eq_candidatePhysicalMarker] at hj
  obtain ⟨selected, hselection, hselectedPayload, _, _, hslot, _, haction, hfeedback, hobservation⟩ :=
    hmarkers u j hj
  exact ⟨selected, hselection, hselectedPayload.trans hpayload.symm,
    hslot, haction, hfeedback, hobservation⟩

/-- Split a stratum source into its SAME retained point and original control. -/
def sourceSplit (z : Z) : X × TimeControl p :=
  (sourceRetained rate rewards C_star C_h q t s hs control0 z,
    originalControl rate rewards C_star C_h q t s hs z)

/-- Recover the complete original source by the accepted inverse split. -/
def sourceRecover (xu : X × TimeControl p) : Z :=
  ⟨ReferenceRetainedSourceCoupling.retainedSourceMap rate rewards C_star C_h q t s hs control0 xu,
    (ReferenceRetainedSourceCoupling.retainedSourceEvent_reconstruct_iff rate rewards C_star C_h q t s hs control0
      xu.1.val xu.2).mpr xu.1.property⟩

theorem measurable_sourceSplit :
    Measurable (sourceSplit rate rewards C_star C_h q t s hs control0) :=
  (measurable_sourceRetained rate rewards C_star C_h q t s hs control0).prodMk
    (measurable_originalControl rate rewards C_star C_h q t s hs)

theorem measurable_sourceRecover :
    Measurable (sourceRecover rate rewards C_star C_h q t s hs control0) :=
  (ReferenceRetainedSourceCoupling.measurable_retainedSourceMap rate rewards C_star C_h q t s hs control0).subtype_mk

/-- Exact recovery of every original source coordinate, including all private
arrays and the original J scalar. -/
theorem sourceRecover_sourceSplit (z : Z) :
    sourceRecover rate rewards C_star C_h q t s hs control0
      (sourceSplit rate rewards C_star C_h q t s hs control0 z) = z := by
  apply Subtype.ext
  change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
    (originalControl rate rewards C_star C_h q t s hs z,
      (sourceRetained rate rewards C_star C_h q t s hs control0 z).val) = z.val
  unfold sourceRetained
  rw [ReferenceTotalSourceDisintegration.sourceRetainedInput_val]
  exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm_apply_apply z.val

theorem sourceSplit_sourceRecover (xu : X × TimeControl p) :
    sourceSplit rate rewards C_star C_h q t s hs control0
      (sourceRecover rate rewards C_star C_h q t s hs control0 xu) = xu := by
  apply Prod.ext
  · apply Subtype.ext
    rw [show (sourceSplit rate rewards C_star C_h q t s hs control0
        (sourceRecover rate rewards C_star C_h q t s hs control0 xu)).1.val =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
        (sourceRecover rate rewards C_star C_h q t s hs control0 xu).val).2 from
      ReferenceTotalSourceDisintegration.sourceRetainedInput_val rate rewards C_star C_h t control0 i0 _]
    exact congrArg Prod.snd ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).apply_symm_apply (xu.2,
      xu.1.val))
  · exact congrArg Prod.fst ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).apply_symm_apply (xu.2,
    xu.1.val))

/-- Lift the admitted original-source product law through the measurable
stratum embedding. No positive-mass premise is needed. -/
theorem sourceRecover_product :
    ((μC).prod ctrlLaw).map (sourceRecover rate rewards C_star C_h q t s hs control0) = μZ := by
  have hE := ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
    rate rewards C_star C_h t control0 i0
  apply (MeasurableEmbedding.subtype_coe hE).map_injective
  rw [Measure.map_map measurable_subtype_coe
    (measurable_sourceRecover rate rewards C_star C_h q t s hs control0),
    ReferenceTotalSourceDisintegration.sourceStratumMeasure_map rate rewards C_star C_h t control0 i0]
  exact ReferenceRetainedSourceCoupling.retainedSourceMap_product rate rewards C_star C_h q t s hs control0

theorem sourceSplit_product :
    (μZ).map (sourceSplit rate rewards C_star C_h q t s hs control0) = (μC).prod ctrlLaw := by
  rw [← sourceRecover_product rate rewards C_star C_h q t s hs control0,
    Measure.map_map (measurable_sourceSplit rate rewards C_star C_h q t s hs control0)
      (measurable_sourceRecover rate rewards C_star C_h q t s hs control0)]
  have heq : sourceSplit rate rewards C_star C_h q t s hs control0 ∘
      sourceRecover rate rewards C_star C_h q t s hs control0 = id :=
    funext (sourceSplit_sourceRecover rate rewards C_star C_h q t s hs control0)
  rw [heq, Measure.map_id]

/-- Split on the literal source branch; its proof supplies exactly Xplus membership. -/
def branchSourceSplit (z : Zplus) : Xplus × TimeControl p :=
  (⟨sourceRetained rate rewards C_star C_h q t s hs control0 z.val, z.property⟩,
    originalControl rate rewards C_star C_h q t s hs z.val)

theorem measurable_branchSourceSplit :
    Measurable (branchSourceSplit rate rewards C_star C_h q t s hs control0) :=
  ((measurable_sourceRetained rate rewards C_star C_h q t s hs control0).comp
    measurable_subtype_coe).subtype_mk.prodMk
      ((measurable_originalControl rate rewards C_star C_h q t s hs).comp measurable_subtype_coe)

/-- On the branch subtype the split still recovers the entire original source. -/
theorem branchSourceSplit_recover (z : Zplus) :
    sourceRecover rate rewards C_star C_h q t s hs control0
      ((branchSourceSplit rate rewards C_star C_h q t s hs control0 z).1.val,
        (branchSourceSplit rate rewards C_star C_h q t s hs control0 z).2) = z.val :=
  sourceRecover_sourceSplit rate rewards C_star C_h q t s hs control0 z.val

/-- The joint branch-source split has precisely the inherited remainder ×
whole-control law. This is the unnormalized original-source transport. -/
theorem branchSourceSplit_product :
    (μZplus).map (branchSourceSplit rate rewards C_star C_h q t s hs control0) = (μCplus).prod ctrlLaw := by
  let forget : Xplus × TimeControl p → X × TimeControl p := Prod.map Subtype.val id
  have hB := ReferenceFirstLiveRecordingBranchMeasurability.measurableSet_continuingRecordingBranch rate rewards C_star
    C_h q t s hs control0
  have hZ := measurableSet_sourceBranch rate rewards C_star C_h q t s hs control0
  have hforget : MeasurableEmbedding forget :=
    (MeasurableEmbedding.subtype_coe hB).prodMap MeasurableEmbedding.id
  apply hforget.map_injective
  rw [Measure.map_map hforget.measurable
    (measurable_branchSourceSplit rate rewards C_star C_h q t s hs control0)]
  have hcomp : forget ∘ branchSourceSplit rate rewards C_star C_h q t s hs control0 =
      sourceSplit rate rewards C_star C_h q t s hs control0 ∘ Subtype.val := rfl
  rw [hcomp, ← Measure.map_map
    (measurable_sourceSplit rate rewards C_star C_h q t s hs control0) measurable_subtype_coe]
  rw [show (μZplus).map (Subtype.val : Zplus → Z) = (μZ).restrict
    {z : Z | Bplus (sourceRetained rate rewards C_star C_h q t s hs control0 z)} from
    map_comap_subtype_coe hZ μZ]
  change ((μZ).restrict ((sourceSplit rate rewards C_star C_h q t s hs control0) ⁻¹'
    (Prod.fst ⁻¹' {x : X | Bplus x}))).map _ = _
  rw [← Measure.restrict_map (measurable_sourceSplit rate rewards C_star C_h q t s hs control0)
    (measurable_fst hB), sourceSplit_product rate rewards C_star C_h q t s hs control0]
  change ((μC).prod ctrlLaw).restrict (Prod.fst ⁻¹' {x : X | Bplus x}) =
    ((μCplus).prod ctrlLaw).map (Prod.map Subtype.val id)
  rw [← Measure.map_prod_map μCplus ctrlLaw measurable_subtype_coe measurable_id,
    Measure.map_id, show (μCplus).map (Subtype.val : Xplus → X) = (μC).restrict {x : X | Bplus x} from
      map_comap_subtype_coe hB μC, Measure.restrict_prod_eq_prod_univ, Set.prod_univ]

/-- Literal actual marker evaluated at the original current control. -/
def sourceMarker (z : Zplus) : Option (Fin p.K) :=
  ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker (branchSourceSplit rate rewards C_star C_h q t s
    hs control0 z)

theorem measurable_sourceMarker :
    Measurable (sourceMarker rate rewards C_star C_h q t s hs control0) :=
  ReferenceFirstLiveRecordingReadoutMeasurability.measurable_currentPhysicalMarker.comp
    (measurable_branchSourceSplit rate rewards C_star C_h q t s hs control0)

/-- The source-stratum incoming template with its WHOLE original rows and J restored. -/
def originalCurrentRecord (z : Z) :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  let input := ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
    (ReferenceTotalSourceDisintegration.sourceIncomingBoundary rate rewards C_star C_h t control0 i0 z) z.val
  ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩

theorem originalCurrentRecord_rows (z : Z) :
    (originalCurrentRecord rate rewards C_star C_h q t s hs control0 z).input.rows = z.val.1.2 := rfl

theorem originalCurrentRecord_selected (z : Z) :
    (originalCurrentRecord rate rewards C_star C_h q t s hs control0 z).input.selected = q :=
  z.property.1

theorem originalCurrentRecord_time (z : Z) :
    (originalCurrentRecord rate rewards C_star C_h q t s hs control0 z).input.time = t := rfl

theorem originalCurrentRecord_rewards (z : Z) :
    (originalCurrentRecord rate rewards C_star C_h q t s hs control0 z).input.rewards =
      rewards := rfl

/-- Actual input identity, rather than equality merely in distribution. -/
theorem sourceInputAtControl_eq_original (z : Z) :
    ReferenceFirstLiveRecordingReadoutMeasurability.sourceInputAtControl (sourceRetained rate rewards C_star C_h q t s
      hs control0 z)
      (originalControl rate rewards C_star C_h q t s hs z) =
    (originalCurrentRecord rate rewards C_star C_h q t s hs control0 z).input := by
  change ReferenceContinuingLiveSlicePreparation.inputAtControl
    (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput rate rewards C_star C_h q t s hs control0
    (sourceRetained rate rewards C_star C_h q t s hs control0 z)) _ = _
  rw [ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_control_eq_retainedGeneratedNextInput]
  exact ReferenceTotalSourceDisintegration.sourceIncomingBoundary_generatedNextInput rate rewards C_star C_h t control0
    i0 z

theorem sourceRecordAtControl_eq_original (z : Z) :
    ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl (sourceRetained rate rewards C_star C_h q t s
      hs control0 z)
      (originalControl rate rewards C_star C_h q t s hs z) =
    originalCurrentRecord rate rewards C_star C_h q t s hs control0 z := by
  exact congrArg (fun input : ReferenceActivePhysicalStep.RoundInput p rate =>
    (⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ :
      ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (sourceInputAtControl_eq_original rate rewards C_star C_h q t s hs control0 z)

/-- The branch-source marker is literally the actual physical record's marker. -/
theorem sourceMarker_eq_original (z : Zplus) :
    sourceMarker rate rewards C_star C_h q t s hs control0 z =
    ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
      (originalCurrentRecord rate rewards C_star C_h q t s hs control0 z.val)
      (ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload
        (branchSourceSplit rate rewards C_star C_h q t s hs control0 z).1) true := by
  unfold sourceMarker ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker
  rw [show ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl
      (branchSourceSplit rate rewards C_star C_h q t s hs control0 z).1.val
      (branchSourceSplit rate rewards C_star C_h q t s hs control0 z).2 =
    originalCurrentRecord rate rewards C_star C_h q t s hs control0 z.val from
      sourceRecordAtControl_eq_original rate rewards C_star C_h q t s hs control0 z.val]

/-- On a recorded original-source arm, the selected actual player observes
the true grid reward. This includes the unoccupied saved-record path and
requires neither positive reward nor eventual delivery. -/
theorem sourceMarker_some_actual_feedback (z : Zplus) (j : Fin p.K)
    (hj : sourceMarker rate rewards C_star C_h q t s hs control0 z = some j) :
    let record := originalCurrentRecord rate rewards C_star C_h q t s hs control0 z.val
    let source := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
        ((record.input.row.2 record.input.time).1))
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected ∧
      selected.view.payload = ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload
        (branchSourceSplit rate rewards C_star C_h q t s hs control0 z).1 ∧
      PublicDiscreteDraws.slotDraw
        (originalControl rate rewards C_star C_h q t s hs z.val).1 = PublicDiscreteDraws.dataSlot ∧
      record.output.preparation.arms.actions source = j ∧
      record.output.preparation.feedback.feedback source = rewards record.input.time j ∧
      (record.output.preparation.feedback.observations source).val.val =
        ((rewards record.input.time j).val : ℝ) / (D p : ℝ) := by
  have hfeedback := currentPhysicalMarker_some_actual_feedback
    rate rewards C_star C_h q t s hs control0
    (branchSourceSplit rate rewards C_star C_h q t s hs control0 z).1
    (originalControl rate rewards C_star C_h q t s hs z.val) j hj
  have hrecord : ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl
      (branchSourceSplit rate rewards C_star C_h q t s hs control0 z).1.val
      (originalControl rate rewards C_star C_h q t s hs z.val) =
      originalCurrentRecord rate rewards C_star C_h q t s hs control0 z.val :=
    sourceRecordAtControl_eq_original rate rewards C_star C_h q t s hs control0 z.val
  dsimp only at hfeedback ⊢
  rw [hrecord] at hfeedback
  exact hfeedback

/-- The original source's literal numerical arm, on the original physical
record. The displayed validity witness is PRODUCED, not a caller premise. -/
theorem sourceMarker_eq_sourceArm (z : Zplus) :
    let x := (branchSourceSplit rate rewards C_star C_h q t s hs control0 z).1
    let input := ReferenceFirstLiveRecordingReadoutMeasurability.sourceCurrentInput x.val
    ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
      ∃ r owned base d hsStart c arm,
      (ReferenceActivePhysicalStep.prepare input).coordinator =
        .live r owned base (.continuingChosen d hsStart c arm) ∧
      (∀ i, ((ReferenceActivePhysicalStep.prepare input).followers.followers i).configuration =
        .ordinary (states i) (memories i)) ∧
      ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload x = r.payload ∧
      (∃ selected : ReferenceActivePhysicalStep.Selection
          (originalCurrentRecord rate rewards C_star C_h q t s hs control0 z.val).input,
        (ReferenceActivePhysicalStep.prepare
          (originalCurrentRecord rate rewards C_star C_h q t s hs control0 z.val).input).coordinator.selection =
            some selected ∧
        selected.view = {
          payload := r.payload
          pendingAtChoice := d.startResult.pending
          cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u
          complementWeights := (ReferenceActivePhysicalStep.liveRegistersAt r input.time).complementWeights } ∧
        (PublicDiscreteDraws.slotDraw (originalControl rate rewards C_star C_h q t s hs z.val).1 =
            PublicDiscreteDraws.dataSlot →
          ∀ i, ((originalCurrentRecord rate rewards C_star C_h q t s hs control0
            z.val).output.preparation.followers.followers i).configuration =
            .ordinary (states i) (memories i))) ∧
      ∃ hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        (originalCurrentRecord rate rewards C_star C_h q t s hs control0 z.val).input.time
        (ReferenceActivePhysicalStep.liveRegistersAt r input.time).complementWeights,
      sourceMarker rate rewards C_star C_h q t s hs control0 z =
        ReferenceFirstWindowNumericalStream.sourceArm
          (originalCurrentRecord rate rewards C_star C_h q t s hs control0 z.val)
          r.payload d.startResult.pending states
          (ReferenceActivePhysicalStep.liveRegistersAt r input.time).complementWeights
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u) hvalid := by
  intro x input
  obtain ⟨states, memories, r, owned, base, d, hsStart, c, arm, hcoord,
      ho, hpayload, hcontrols, hdata, hnum⟩ :=
    currentPhysicalMarker_eq_sourceArm rate rewards C_star C_h q t s hs control0 x
  let u := (branchSourceSplit rate rewards C_star C_h q t s hs control0 z).2
  have hrecord : ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl x.val u =
      originalCurrentRecord rate rewards C_star C_h q t s hs control0 z.val :=
    sourceRecordAtControl_eq_original rate rewards C_star C_h q t s hs control0 z.val
  obtain ⟨c_u, arm_u, hcoord_u⟩ := hcontrols u
  let selected := ReferenceContinuingLiveSlicePreparation.continuingSelection
    (ReferenceFirstLiveRecordingReadoutMeasurability.sourceInputAtControl x.val u)
    r owned base d hsStart c_u arm_u
  have hselected := ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
    (ReferenceFirstLiveRecordingReadoutMeasurability.sourceInputAtControl x.val u)
    r owned base d hsStart c_u arm_u hcoord_u
  have hcurrent : ∃ chosen : ReferenceActivePhysicalStep.Selection
      (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl x.val u).input,
      (ReferenceActivePhysicalStep.prepare
        (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl x.val u).input).coordinator.selection =
          some chosen ∧
      chosen.view = {
        payload := r.payload
        pendingAtChoice := d.startResult.pending
        cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u
        complementWeights := (ReferenceActivePhysicalStep.liveRegistersAt r input.time).complementWeights } ∧
      (PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.dataSlot →
        ∀ i, ((ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl x.val
          u).output.preparation.followers.followers i).configuration =
          .ordinary (states i) (memories i)) :=
    ⟨selected, hselected, rfl, hdata u⟩
  rw [hrecord] at hcurrent
  have hnum' : ∃ hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl x.val u).input.time
      (ReferenceActivePhysicalStep.liveRegistersAt r input.time).complementWeights,
      sourceMarker rate rewards C_star C_h q t s hs control0 z =
        ReferenceFirstWindowNumericalStream.sourceArm
          (ReferenceFirstLiveRecordingReadoutMeasurability.sourceRecordAtControl x.val u)
          r.payload d.startResult.pending states
          (ReferenceActivePhysicalStep.liveRegistersAt r input.time).complementWeights
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u) hvalid :=
    ⟨arm.choiceInputsValid, hnum u⟩
  rw [hrecord] at hnum'
  exact ⟨states, memories, r, owned, base, d, hsStart, c, arm, hcoord, ho, hpayload, hcurrent, hnum'⟩

/-- The FIRST round has an empty continuing domain, so both inherited branch
measures vanish. No continuing constructor or frozen FIRST payload is used. -/
theorem branch_measures_eq_zero_of_s_eq_t (hfirst : s = t.val) :
    μCplus = 0 ∧ μZplus = 0 := by
  have hempty := ReferenceFirstLiveRecordingBranchMeasurability.continuingRecordingBranch_eq_empty_of_offset_eq_zero
    rate rewards C_star C_h q t s hs control0 (by omega)
  let : IsEmpty Xplus := ⟨fun x => by
    have hx : x.val ∈ {y : X | Bplus y} := x.property
    rw [hempty] at hx
    exact hx⟩
  let : IsEmpty Zplus := ⟨fun z => isEmptyElim
    (branchSourceSplit rate rewards C_star C_h q t s hs control0 z).1⟩
  exact ⟨Measure.eq_zero_of_isEmpty μCplus, Measure.eq_zero_of_isEmpty μZplus⟩

/-- The actual marker kernel's atom mass on its literal branch domain. -/
def markerMass (x : Xplus) (o : Option (Fin p.K)) : ℝ≥0∞ :=
  match o with
  | some j => ENNReal.ofReal (markerRate rate rewards C_star C_h q t s hs control0 x j)
  | none => ENNReal.ofReal (1 - ∑ j : Fin p.K,
      markerRate rate rewards C_star C_h q t s hs control0 x j)

theorem measurable_markerMass (o : Option (Fin p.K)) :
    Measurable (fun x : Xplus => markerMass rate rewards C_star C_h q t s hs control0 x o) := by
  cases o with
  | some j => exact (measurable_markerRate rate rewards C_star C_h q t s hs control0 j).ennreal_ofReal
  | none =>
      apply Measurable.ennreal_ofReal
      exact measurable_const.sub (Finset.measurable_sum _ fun j _ =>
        measurable_markerRate rate rewards C_star C_h q t s hs control0 j)

theorem currentPhysicalMarker_mass (x : Xplus) (o : Option (Fin p.K)) :
    ctrlLaw {u | ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker (x, u) = o} =
      markerMass rate rewards C_star C_h q t s hs control0 x o := by
  cases o with
  | some j => exact (currentPhysicalMarker_masses rate rewards C_star C_h q t s hs control0 x).1 j
  | none => exact (currentPhysicalMarker_masses rate rewards C_star C_h q t s hs control0 x).2

/-- Joint Borel cylinder on the branch remainder and WHOLE current control. -/
theorem measurableSet_markerCylinder (Aset : Set X) (hAset : MeasurableSet Aset)
    (o : Option (Fin p.K)) :
    MeasurableSet {xu : Xplus × TimeControl p | xu.1.val ∈ Aset ∧
      ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker xu = o} :=
  (hAset.preimage (measurable_subtype_coe.comp measurable_fst)).inter
    (measurableSet_eq_fun ReferenceFirstLiveRecordingReadoutMeasurability.measurable_currentPhysicalMarker
      measurable_const)

theorem measurableSet_sourceCylinder (Aset : Set X) (hAset : MeasurableSet Aset)
    (o : Option (Fin p.K)) :
    MeasurableSet {z : Zplus |
      sourceRetained rate rewards C_star C_h q t s hs control0 z.val ∈ Aset ∧
      sourceMarker rate rewards C_star C_h q t s hs control0 z = o} :=
  (measurableSet_markerCylinder rate rewards C_star C_h q t s hs control0 Aset hAset o).preimage
    (measurable_branchSourceSplit rate rewards C_star C_h q t s hs control0)

/-- The original-source cylinder, with the actual selected payload varying
over the branch and with no normalization or extra launch/J factor. -/
theorem original_source_cylinder (Aset : Set X) (hAset : MeasurableSet Aset)
    (o : Option (Fin p.K)) :
    μZplus {z : Zplus |
      sourceRetained rate rewards C_star C_h q t s hs control0 z.val ∈ Aset ∧
      sourceMarker rate rewards C_star C_h q t s hs control0 z = o} =
    ∫⁻ x : Xplus in {x | x.val ∈ Aset},
      markerMass rate rewards C_star C_h q t s hs control0 x o ∂μCplus := by
  classical
  have hC := measurableSet_markerCylinder rate rewards C_star C_h q t s hs control0 Aset hAset o
  have hmap := congrArg (fun μ : Measure (Xplus × TimeControl p) =>
      μ {xu | xu.1.val ∈ Aset ∧
        ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker xu = o})
    (branchSourceSplit_product rate rewards C_star C_h q t s hs control0)
  rw [Measure.map_apply (measurable_branchSourceSplit rate rewards C_star C_h q t s hs control0)
    hC, Measure.prod_apply hC] at hmap
  change μZplus {z : Zplus |
    sourceRetained rate rewards C_star C_h q t s hs control0 z.val ∈ Aset ∧
    sourceMarker rate rewards C_star C_h q t s hs control0 z = o} = _ at hmap
  have hAplus : MeasurableSet {x : Xplus | x.val ∈ Aset} :=
    hAset.preimage measurable_subtype_coe
  rw [hmap, ← lintegral_indicator hAplus]
  apply lintegral_congr
  intro x
  by_cases hx : x.val ∈ Aset
  · simp only [Set.indicator_of_mem (show x ∈ {y : Xplus | y.val ∈ Aset} from hx)]
    have hevent : Prod.mk x ⁻¹' {xu : Xplus × TimeControl p |
        xu.1.val ∈ Aset ∧ ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker xu = o} =
        {u | ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker (x, u) = o} := by
      ext u
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hx, true_and]
    rw [hevent]
    exact currentPhysicalMarker_mass rate rewards C_star C_h q t s hs control0 x o
  · have hevent : Prod.mk x ⁻¹' {xu : Xplus × TimeControl p |
        xu.1.val ∈ Aset ∧ ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker xu = o} = ∅ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hx, false_and, Set.mem_empty_iff_false]
    rw [hevent, measure_empty, Set.indicator_of_notMem (show x ∉ {y : Xplus | y.val ∈ Aset} from hx)]

theorem original_source_cylinder_some (Aset : Set X) (hAset : MeasurableSet Aset)
    (j : Fin p.K) :
    μZplus {z : Zplus |
      sourceRetained rate rewards C_star C_h q t s hs control0 z.val ∈ Aset ∧
      sourceMarker rate rewards C_star C_h q t s hs control0 z = some j} =
    ∫⁻ x : Xplus in {x | x.val ∈ Aset},
      ENNReal.ofReal (markerRate rate rewards C_star C_h q t s hs control0 x j) ∂μCplus :=
  original_source_cylinder rate rewards C_star C_h q t s hs control0 Aset hAset (some j)

theorem original_source_cylinder_none (Aset : Set X) (hAset : MeasurableSet Aset) :
    μZplus {z : Zplus |
      sourceRetained rate rewards C_star C_h q t s hs control0 z.val ∈ Aset ∧
      sourceMarker rate rewards C_star C_h q t s hs control0 z = none} =
    ∫⁻ x : Xplus in {x | x.val ∈ Aset},
      ENNReal.ofReal (1 - ∑ j : Fin p.K,
        markerRate rate rewards C_star C_h q t s hs control0 x j) ∂μCplus :=
  original_source_cylinder rate rewards C_star C_h q t s hs control0 Aset hAset none

/-- The same event under μZ explicitly retains its computed Bplus membership.
The existential proof only forms the branch subtype; there is no off-branch marker. -/
theorem sourceCylinder_eq_stratum_event (Aset : Set X) (o : Option (Fin p.K)) :
    μZplus {z : Zplus |
      sourceRetained rate rewards C_star C_h q t s hs control0 z.val ∈ Aset ∧
      sourceMarker rate rewards C_star C_h q t s hs control0 z = o} =
    μZ {z : Z | ∃ hz : Bplus (sourceRetained rate rewards C_star C_h q t s hs control0 z),
      sourceRetained rate rewards C_star C_h q t s hs control0 z ∈ Aset ∧
      sourceMarker rate rewards C_star C_h q t s hs control0 ⟨z, hz⟩ = o} := by
  calc
    _ = μZ (Subtype.val '' {z : Zplus |
        sourceRetained rate rewards C_star C_h q t s hs control0 z.val ∈ Aset ∧
        sourceMarker rate rewards C_star C_h q t s hs control0 z = o}) :=
      comap_subtype_coe_apply
        (measurableSet_sourceBranch rate rewards C_star C_h q t s hs control0) μZ _
    _ = _ := by
      congr 1
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, hy⟩
      · rintro ⟨hz, hA, hmarker⟩
        exact ⟨⟨z, hz⟩, ⟨hA, hmarker⟩, rfl⟩

theorem measurableSet_stratumCylinder (Aset : Set X) (hAset : MeasurableSet Aset)
    (o : Option (Fin p.K)) :
    MeasurableSet {z : Z | ∃ hz : Bplus (sourceRetained rate rewards C_star C_h q t s hs control0 z),
      sourceRetained rate rewards C_star C_h q t s hs control0 z ∈ Aset ∧
      sourceMarker rate rewards C_star C_h q t s hs control0 ⟨z, hz⟩ = o} := by
  have himage := (MeasurableEmbedding.subtype_coe
    (measurableSet_sourceBranch rate rewards C_star C_h q t s hs control0)).measurableSet_image.mpr
      (measurableSet_sourceCylinder rate rewards C_star C_h q t s hs control0 Aset hAset o)
  convert himage using 1
  ext z
  constructor
  · rintro ⟨hz, hA, hmarker⟩
    exact ⟨⟨z, hz⟩, ⟨hA, hmarker⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩

/-- Cylinder formula directly under the inherited original source stratum. -/
theorem stratum_source_cylinder (Aset : Set X) (hAset : MeasurableSet Aset)
    (o : Option (Fin p.K)) :
    μZ {z : Z | ∃ hz : Bplus (sourceRetained rate rewards C_star C_h q t s hs control0 z),
      sourceRetained rate rewards C_star C_h q t s hs control0 z ∈ Aset ∧
      sourceMarker rate rewards C_star C_h q t s hs control0 ⟨z, hz⟩ = o} =
    ∫⁻ x : Xplus in {x | x.val ∈ Aset},
      markerMass rate rewards C_star C_h q t s hs control0 x o ∂μCplus := by
  rw [← sourceCylinder_eq_stratum_event rate rewards C_star C_h q t s hs control0]
  exact original_source_cylinder rate rewards C_star C_h q t s hs control0 Aset hAset o

end Bandits.Support.ReferenceFirstLiveRecordingSourceCylinder

end
