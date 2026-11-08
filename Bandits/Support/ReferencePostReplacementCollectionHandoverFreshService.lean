/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionHandoverPredictableSupport
public import Bandits.Support.ReferencePostReplacementCollectionHandoverDecoderCorrespondence
public import Bandits.Support.ReferenceFirstLiveHandoverConfirmationService

/-!
# Original-source fresh service for later H handovers

The two service stages are the actual successful `StartRound` status at the
current H choice. The physical service events are the global raw DOWN events;
this module does not use first-live windows or a stopped phase replay.

Sources: `05_binary_transport.tex:244-289`,
`06_interruptions.tex:246-299,431-490`, and
`appendix_a_local_protocol.tex:28-79` in the pinned ZIP4 manuscript.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Bandits.Support ConstructorDimensions BootstrapPrivateRoundStreams
open ContinuousLearningRows
open scoped Classical ENNReal

namespace Bandits.Support.ReferencePostReplacementCollectionHandoverFreshService

open ReferencePostReplacementCollectionHandoverPredictableSupport
open ReferencePostReplacementCollectionHandoverSourcePrefix
open ReferencePostReplacementCollectionHandoverDecoderCorrespondence
open ReferenceFirstLiveHandoverBoundaryFactorization
open ReferenceFirstLiveHandoverConfirmationService
open ReferenceFixedTimeSourceControlCoupling
open ReferenceSourcePrefixHistoryFiltration

abbrev Source := BootstrapPrivateRoundStreams.SourceInput

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "F" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0

/-- The literal successful local `StartRound` code at the actual pre-round
source input. -/
def startCode (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source p) :=
  ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
    rate rewards C_star C_h t i z

/-- The original raw H task stage before this follower has accepted its
current DOWN word. -/
def A_before (t : Fin p.T) (i : Fin (p.m - 1)) : Set (Source p) :=
  {z | rawHTaskSupport rate rewards C_star C_h t i z ∧
    ∃ state memory,
      startCode rate rewards C_star C_h t i z =
        .inr (.success state memory) ∧ state.status = 0}

/-- The original raw H task stage after this follower has accepted its current
DOWN word but before its confirmation. -/
def A_after (t : Fin p.T) (i : Fin (p.m - 1)) : Set (Source p) :=
  {z | rawHTaskSupport rate rewards C_star C_h t i z ∧
    ∃ state memory,
      startCode rate rewards C_star C_h t i z =
        .inr (.success state memory) ∧ state.status = 1}

/-- The pre-acceptance physical service indicator on the whole original source. -/
def X_before (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source p) : ℝ :=
  (if z ∈ A_before rate rewards C_star C_h t i then 1 else 0) *
    (if V_before rate rewards C_star C_h i t z then 1 else 0)

/-- The accepted-word physical service indicator on the whole original source. -/
def X_after (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source p) : ℝ :=
  (if z ∈ A_after rate rewards C_star C_h t i then 1 else 0) *
    (if V_after rate rewards C_star C_h i t z then 1 else 0)

/-- The instantaneous source coefficient, using the whole reward row. -/
def serviceCoefficient (t : Fin p.T) : ℝ :=
  ((Finset.univ.filter fun a : Fin p.K => 0 < (rewards t a).val).card : ℝ) /
    (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))

private theorem startCode_status_set_measurable (t : Fin p.T) (i : Fin (p.m - 1))
    (s : Fin 3) :
    MeasurableSet[F (t.val + 1)]
      {z : Source p | ∃ state memory,
        startCode rate rewards C_star C_h t i z =
          .inr (.success state memory) ∧ state.status = s} := by
  let S : Set (Unit ⊕ FollowerLifecycleMeasurability.StartRoundResultCode p rate) :=
    {c | ∃ state memory, c = .inr (.success state memory) ∧ state.status = s}
  have hS : MeasurableSet S := by
    rw [measurableSet_sum_iff]
    constructor
    · simp [S]
    · exact MeasurableSet.of_discrete
  have hcode := ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_measurable
    rate rewards C_star C_h control0 t i
  change MeasurableSet[F (t.val + 1)]
    {z : Source p | startCode rate rewards C_star C_h t i z ∈ S}
  exact hcode hS

/-- The before and after source stages are predictable in the original
pre-round source filtration. -/
theorem measurableSet_A_before (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[F (t.val + 1)] (A_before rate rewards C_star C_h t i) := by
  unfold A_before
  exact (rawHTaskSupport_measurableSet rate rewards C_star C_h control0 t i).inter
    (startCode_status_set_measurable rate rewards C_star C_h control0 t i 0)

/-- The accepted stage is predictable in the same original pre-round field. -/
theorem measurableSet_A_after (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[F (t.val + 1)] (A_after rate rewards C_star C_h t i) := by
  unfold A_after
  exact (rawHTaskSupport_measurableSet rate rewards C_star C_h control0 t i).inter
    (startCode_status_set_measurable rate rewards C_star C_h control0 t i 1)

/-- Both literal stages are invariant under replacing the source suffix at the
current date. This is only a support/code factorization, not a service claim. -/
theorem A_before_factor (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source p) :
    z ∈ A_before rate rewards C_star C_h t i ↔
      sourcePrefix control0 t.val z ∈ A_before rate rewards C_star C_h t i := by
  change (rawHTaskSupport rate rewards C_star C_h t i z ∧
      ∃ state memory,
        ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
          rate rewards C_star C_h t i z = .inr (.success state memory) ∧ state.status = 0) ↔
    (rawHTaskSupport rate rewards C_star C_h t i
        (sourcePrefix control0 t.val z) ∧
      ∃ state memory,
        ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
          rate rewards C_star C_h t i (sourcePrefix control0 t.val z) =
            .inr (.success state memory) ∧ state.status = 0)
  rw [rawHTaskSupport_factor rate rewards C_star C_h control0 z t i,
    ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_factor
      rate rewards C_star C_h control0 t i z]

/-- The accepted stage has the same strict-past factorization. -/
theorem A_after_factor (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source p) :
    z ∈ A_after rate rewards C_star C_h t i ↔
      sourcePrefix control0 t.val z ∈ A_after rate rewards C_star C_h t i := by
  change (rawHTaskSupport rate rewards C_star C_h t i z ∧
      ∃ state memory,
        ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
          rate rewards C_star C_h t i z = .inr (.success state memory) ∧ state.status = 1) ↔
    (rawHTaskSupport rate rewards C_star C_h t i
        (sourcePrefix control0 t.val z) ∧
      ∃ state memory,
        ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
          rate rewards C_star C_h t i (sourcePrefix control0 t.val z) =
            .inr (.success state memory) ∧ state.status = 1)
  rw [rawHTaskSupport_factor rate rewards C_star C_h control0 z t i,
    ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_factor
      rate rewards C_star C_h control0 t i z]

private theorem actualHandover_index (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : Source p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (j : Fin (actualHandoverRecords rate rewards C_star C_h z b).length) :
    ∃ hk : b.val + j.val <
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length,
      (actualHandoverRecords rate rewards C_star C_h z b).get j =
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get
          ⟨b.val + j.val, hk⟩ := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b.val + 1)
  let V := R[b.val] :: W
  let H := actualHandoverRecords rate rewards C_star C_h z b
  have hV : V.IsPrefix (R.drop b.val) := by
    rw [List.drop_eq_getElem_cons b.isLt]
    exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
  have hH : H.IsPrefix (R.drop b.val) := by
    dsimp [H, actualHandoverRecords, V]
    exact (List.takeWhile_prefix _).trans hV
  have hlen : H.length ≤ R.length - b.val := by
    simpa only [List.length_drop] using hH.length_le
  have hlen' : (actualHandoverRecords rate rewards C_star C_h z b).length ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length -
        b.val := by
    simpa only [H, R] using hlen
  have hj' : j.val < (actualHandoverRecords rate rewards C_star C_h z b).length := j.isLt
  have hk : b.val + j.val <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length := by
    omega
  refine ⟨hk, ?_⟩
  change H[j.val] = R[b.val + j.val]'hk
  rw [hH.getElem j.isLt, List.getElem_drop]

private theorem actualHandover_lookup (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : Source p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (j : Fin (actualHandoverRecords rate rewards C_star C_h z b).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      ((actualHandoverRecords rate rewards C_star C_h z b)[j.val]).input.time z =
      some ((actualHandoverRecords rate rewards C_star C_h z b)[j.val]) := by
  obtain ⟨hk, heq⟩ := actualHandover_index rate rewards C_star C_h z b j
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let H := actualHandoverRecords rate rewards C_star C_h z b
  have heq' : H[j.val] = R[b.val + j.val]'hk := by
    simpa only [List.get_eq_getElem] using heq
  rw [heq']
  have htime := completeSuffixRecord_time rate rewards C_star C_h z ⟨b.val + j.val, hk⟩
  have htime' : (R[b.val + j.val]'hk).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (b.val + j.val) := by
    simpa only [List.get_eq_getElem] using htime
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
      (R[b.val + j.val]'hk).input.time.val := by rw [htime']; omega
  have hindex : (R[b.val + j.val]'hk).input.time.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = b.val + j.val := by
    rw [htime']
    omega
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left hstart, hindex]
  exact List.getElem?_eq_getElem hk

private theorem rawHTaskSupport_startCode_before_or_after (t : Fin p.T)
    (i : Fin (p.m - 1)) (z : Source p)
    (hsupport : rawHTaskSupport rate rewards C_star C_h t i z) :
    (∃ state memory, startCode rate rewards C_star C_h t i z =
      .inr (.success state memory) ∧ state.status = 0) ∨
    (∃ state memory, startCode rate rewards C_star C_h t i z =
      .inr (.success state memory) ∧ state.status = 1) := by
  classical
  obtain ⟨record, hrecordMem, htime, selected, hselected, hi⟩ := hsupport
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [] := by
    intro hnil
    simp [rawHRecords, hnil] at hrecordMem
  rcases rawH_endpoint_cases rate rewards C_star C_h z hK with hnil | hendpoint
  · rcases hnil with ⟨hrecords, _, _⟩
    rw [hrecords] at hrecordMem
    cases hrecordMem
  · rcases hendpoint with ⟨b, _, hlater, _, _, _, _, _, hrecords⟩
    let H := actualHandoverRecords rate rewards C_star C_h z b
    have hmemH : record ∈ H := by
      change record ∈ (R[b.val] ::
        ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)).takeWhile
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
      rw [← hrecords]
      exact hrecordMem
    obtain ⟨jn, hjn, hrecordEq⟩ := List.mem_iff_getElem.mp hmemH
    let j : Fin H.length := ⟨jn, hjn⟩
    have hrecordEq' : H[j.val] = record := by simpa only [j] using hrecordEq
    subst record
    have hlookup : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h H[j.val].input.time z = some H[j.val] := by
      simpa only [H] using actualHandover_lookup rate rewards C_star C_h z b j
    have hdecode := actual_later_handover_decoder_correspondence
      (rate := rate) rewards C_star C_h z b hlater i
    obtain ⟨birthPayload, before, beforeMemory, _hbirth, _hbirthInput,
      _hbefore, _hstrict, hframes⟩ := hdecode
    obtain ⟨selectedFrame, states, memories, inputState, inputMemory,
      hselFrame, hpayloadFrame, hpreparedFrame, hinputFrame, _hbank,
      _hchoiceBank, _hsnapshot, _hrest⟩ := hframes j
    have hsel : H[j.val].output.preparation.coordinator.selection = some selected :=
      hselected
    have hselEq := Option.some.inj (hselFrame.symm.trans hsel)
    subst selectedFrame
    have hstageAll :=
      ReferencePostReplacementCollectionHandoverReplay.actual_later_installation_handover_choice_stages
      rate rewards C_star C_h z b
    rw [ite_eq_left hlater] at hstageAll
    obtain ⟨stagePayload, _hbirthStage, hstageFrames⟩ := hstageAll
    obtain ⟨_before, _beforeMemory, _hinputBirth, _hunoccupied, _hstrictStart,
      hstageAt⟩ := hstageFrames i
    obtain ⟨selectedStage, choice, choiceMemory, hselStage, hpayloadStage,
      hchoiceStage, hcase⟩ := hstageAt j
    have hselStageEq := Option.some.inj (hselStage.symm.trans hsel)
    subst selectedStage
    have hpayloadEq : birthPayload = stagePayload := hpayloadFrame.symm.trans hpayloadStage
    subst stagePayload
    obtain ⟨inputChoice, hinputChoice, hcode⟩ :=
      ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_actual_choice
        rate rewards C_star C_h t i z H[j.val] inputState inputMemory
        (by rw [← htime]; exact hlookup) hinputFrame
    have hchoiceEq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hchoiceStage.symm.trans hinputChoice)
    have hstatusEq : inputChoice.status = choice.status := congrArg
      (fun state : ReferencePrelaunchFollower.State p rate.eta => state.status)
        hchoiceEq.1.symm
    rcases hcase with hUnoccupied | hRest
    · rcases hUnoccupied with ⟨_, hu, _, _⟩
      left
      refine ⟨FollowerDownMeasurability.followerStateCode rate inputChoice,
        FollowerLifecycleMeasurability.localMemoryCode inputMemory, hcode, ?_⟩
      simp [FollowerDownMeasurability.followerStateCode,
        FollowerDownMeasurability.followerStatusCode, hstatusEq, hu]
    · rcases hRest with hPending | hRemoved
      · rcases hPending with ⟨_, hpending, _, _⟩
        right
        refine ⟨FollowerDownMeasurability.followerStateCode rate inputChoice,
          FollowerLifecycleMeasurability.localMemoryCode inputMemory, hcode, ?_⟩
        simp [FollowerDownMeasurability.followerStateCode,
          FollowerDownMeasurability.followerStatusCode, hstatusEq, hpending]
      · rcases hRemoved with ⟨hnotSelected, _, _, _⟩
        exact False.elim (hnotSelected hi)

/- The two actual `StartRound` stages are disjoint. -/
theorem A_before_disjoint_A_after (t : Fin p.T) (i : Fin (p.m - 1)) :
    Disjoint (A_before rate rewards C_star C_h t i)
      (A_after rate rewards C_star C_h t i) := by
  refine Set.disjoint_left.mpr ?_
  intro z hb ha
  rcases hb.2 with ⟨state, memory, hcode, hzero⟩
  rcases ha.2 with ⟨state', memory', hcode', hone⟩
  have hcodes := hcode.symm.trans hcode'
  have hstatus : state.status = state'.status := by
    have h := congrArg (fun code : Unit ⊕ FollowerLifecycleMeasurability.StartRoundResultCode p rate =>
      match code with
      | .inr (.success s _) => s.status
      | _ => 2) hcodes
    simpa using h
  rw [hstatus] at hzero
  exact (by decide : (0 : Fin 3) ≠ 1) (hzero.symm.trans hone)

/- Every literal raw H task belongs to exactly one of the actual before and
after `StartRound` stages. -/
theorem rawHTaskSupport_partition (t : Fin p.T) (i : Fin (p.m - 1)) :
    {z | rawHTaskSupport rate rewards C_star C_h t i z} =
      A_before rate rewards C_star C_h t i ∪ A_after rate rewards C_star C_h t i := by
  ext z
  constructor
  · intro h
    rcases rawHTaskSupport_startCode_before_or_after rate rewards C_star C_h t i z h with hbefore | hafter
    · exact Or.inl ⟨h, hbefore⟩
    · exact Or.inr ⟨h, hafter⟩
  · intro h
    rcases h with hbefore | hafter
    · exact hbefore.1
    · exact hafter.1

/-- A source-prefix predictable mask can be pulled through the global raw
before-service conditional law. -/
theorem before_condExp_integral (t : Fin p.T) (i : Fin (p.m - 1)) :
    μ[(fun z => X_before rate rewards C_star C_h t i z) | F (t.val + 1)] =ᵐ[μ]
      fun z => (if z ∈ A_before rate rewards C_star C_h t i then (1 : ℝ) else 0) *
        ∫ control,
          (if V_before rate rewards C_star C_h i t
            (replaceSourceControl p t (sourcePrefix control0 t.val z) control)
           then (1 : ℝ) else 0) ∂ContinuousLearningRows.timeControlLaw p := by
  classical
  let E := A_before rate rewards C_star C_h t i
  let f : Source p → ℝ := fun z =>
    if V_before rate rewards C_star C_h i t z then 1 else 0
  let g : Source p → ℝ := fun z => if z ∈ E then 1 else 0
  let μs := BootstrapPrivateRoundStreams.sourceInputLaw p
  let Ht := F (t.val + 1)
  let Hnext := F (t.val + 2)
  let mΩ : MeasurableSpace (Source p) := Prod.instMeasurableSpace
  have hE : MeasurableSet[Ht] E := by
    dsimp [Ht, E]
    exact measurableSet_A_before rate rewards C_star C_h control0 t i
  have hg : StronglyMeasurable[Ht] g := by
    change StronglyMeasurable[Ht]
      (E.indicator fun _ : Source p => (1 : ℝ))
    exact stronglyMeasurable_const.indicator hE
  have hfield : Ht ≤ Hnext := by
    dsimp [Ht, Hnext]
    exact (sourcePrefixFiltration control0).mono (by omega)
  have hf : StronglyMeasurable[Hnext] f := by
    dsimp [Hnext, f]
    exact V_before_roundEnd_stronglyMeasurable rate rewards C_star C_h control0 i t
  have hambient : Hnext ≤ mΩ := by
    dsimp [Hnext]
    simpa [mΩ] using (sourcePrefixFiltration control0).le (t.val + 2)
  have hfAmbient : StronglyMeasurable f := by
    simpa [mΩ] using hf.mono hambient
  have hfgAmbient : StronglyMeasurable (fun z => g z * f z) := by
    have hgAmbient : StronglyMeasurable g := by
      simpa [mΩ] using hg.mono (hfield.trans hambient)
    exact hgAmbient.mul hfAmbient
  have hnormf : ∀ z, ‖f z‖ ≤ (1 : ℝ) := by
    intro z
    by_cases hv : V_before rate rewards C_star C_h i t z <;> simp [f, hv]
  have hnormfg : ∀ z, ‖g z * f z‖ ≤ (1 : ℝ) := by
    intro z
    by_cases hEz : z ∈ E <;>
      by_cases hVz : V_before rate rewards C_star C_h i t z <;>
      simp [g, f, hEz, hVz]
  have hfInt : Integrable f μs := by
    refine (integrable_const (1 : ℝ)).mono' hfAmbient.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hnormf
  have hprodInt : Integrable (fun z => g z * f z) μs := by
    refine (integrable_const (1 : ℝ)).mono' hfgAmbient.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hnormfg
  have hpull := condExp_mul_of_stronglyMeasurable_left hg hprodInt hfInt
  have hraw := V_before_condExp rate rewards C_star C_h control0 i t
  have hfinal :
      μs[(fun z => g z * f z) | Ht] =ᵐ[μs] fun z =>
        g z * ∫ control, (if V_before rate rewards C_star C_h i t
          (replaceSourceControl p t (sourcePrefix control0 t.val z) control)
          then (1 : ℝ) else 0) ∂ContinuousLearningRows.timeControlLaw p := by
    filter_upwards [hpull, hraw] with z hpull hz
    calc
      μs[(fun z => g z * f z) | Ht] z = g z * μs[f | Ht] z := hpull
      _ = g z * ∫ control, (if V_before rate rewards C_star C_h i t
          (replaceSourceControl p t (sourcePrefix control0 t.val z) control)
          then (1 : ℝ) else 0) ∂ContinuousLearningRows.timeControlLaw p := by rw [hz]
  exact hfinal

/-- The corresponding predictable-mask reduction for after-service. -/
theorem after_condExp_integral (t : Fin p.T) (i : Fin (p.m - 1)) :
    μ[(fun z => X_after rate rewards C_star C_h t i z) | F (t.val + 1)] =ᵐ[μ]
      fun z => (if z ∈ A_after rate rewards C_star C_h t i then (1 : ℝ) else 0) *
        ∫ control,
          (if V_after rate rewards C_star C_h i t
            (replaceSourceControl p t (sourcePrefix control0 t.val z) control)
           then (1 : ℝ) else 0) ∂ContinuousLearningRows.timeControlLaw p := by
  classical
  let E := A_after rate rewards C_star C_h t i
  let f : Source p → ℝ := fun z =>
    if V_after rate rewards C_star C_h i t z then 1 else 0
  let g : Source p → ℝ := fun z => if z ∈ E then 1 else 0
  let μs := BootstrapPrivateRoundStreams.sourceInputLaw p
  let Ht := F (t.val + 1)
  let Hnext := F (t.val + 2)
  let mΩ : MeasurableSpace (Source p) := Prod.instMeasurableSpace
  have hE : MeasurableSet[Ht] E := by
    dsimp [Ht, E]
    exact measurableSet_A_after rate rewards C_star C_h control0 t i
  have hg : StronglyMeasurable[Ht] g := by
    change StronglyMeasurable[Ht]
      (E.indicator fun _ : Source p => (1 : ℝ))
    exact stronglyMeasurable_const.indicator hE
  have hfield : Ht ≤ Hnext := by
    dsimp [Ht, Hnext]
    exact (sourcePrefixFiltration control0).mono (by omega)
  have hf : StronglyMeasurable[Hnext] f := by
    dsimp [Hnext, f]
    exact V_after_roundEnd_stronglyMeasurable rate rewards C_star C_h control0 i t
  have hambient : Hnext ≤ mΩ := by
    dsimp [Hnext]
    simpa [mΩ] using (sourcePrefixFiltration control0).le (t.val + 2)
  have hfAmbient : StronglyMeasurable f := by
    simpa [mΩ] using hf.mono hambient
  have hfgAmbient : StronglyMeasurable (fun z => g z * f z) := by
    have hgAmbient : StronglyMeasurable g := by
      simpa [mΩ] using hg.mono (hfield.trans hambient)
    exact hgAmbient.mul hfAmbient
  have hnormf : ∀ z, ‖f z‖ ≤ (1 : ℝ) := by
    intro z
    by_cases hv : V_after rate rewards C_star C_h i t z <;> simp [f, hv]
  have hnormfg : ∀ z, ‖g z * f z‖ ≤ (1 : ℝ) := by
    intro z
    by_cases hEz : z ∈ E <;>
      by_cases hVz : V_after rate rewards C_star C_h i t z <;>
      simp [g, f, hEz, hVz]
  have hfInt : Integrable f μs := by
    refine (integrable_const (1 : ℝ)).mono' hfAmbient.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hnormf
  have hprodInt : Integrable (fun z => g z * f z) μs := by
    refine (integrable_const (1 : ℝ)).mono' hfgAmbient.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hnormfg
  have hpull := condExp_mul_of_stronglyMeasurable_left hg hprodInt hfInt
  have hraw := V_after_condExp rate rewards C_star C_h control0 i t
  have hfinal :
      μs[(fun z => g z * f z) | Ht] =ᵐ[μs] fun z =>
        g z * ∫ control, (if V_after rate rewards C_star C_h i t
          (replaceSourceControl p t (sourcePrefix control0 t.val z) control)
          then (1 : ℝ) else 0) ∂ContinuousLearningRows.timeControlLaw p := by
    filter_upwards [hpull, hraw] with z hpull hz
    calc
      μs[(fun z => g z * f z) | Ht] z = g z * μs[f | Ht] z := hpull
      _ = g z * ∫ control, (if V_after rate rewards C_star C_h i t
          (replaceSourceControl p t (sourcePrefix control0 t.val z) control)
          then (1 : ℝ) else 0) ∂ContinuousLearningRows.timeControlLaw p := by rw [hz]
  exact hfinal

/-- The actual H support supplies the entire ordinary physical action frame.
The successful start code names the CHOICE state, before current feedback. -/
theorem actual_task_frame (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source p)
    (hsupport : rawHTaskSupport rate rewards C_star C_h t i z) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection record.input)
      (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      actualRecord rate rewards C_star C_h t z = some record ∧
      record.output.preparation.coordinator.selection = some selected ∧
      i ∈ selected.view.pendingAtChoice ∧
      (∀ j, (record.output.preparation.followers.followers j).configuration =
        .ordinary (states j) (memories j)) ∧
      (∀ j, (states j).status ≠ .unoccupied →
        (states j).lastDown = some (selected.view.payload.downRecord j)) ∧
      (∀ j, (states j).status ≠ .released) ∧
      startCode rate rewards C_star C_h t i z = .inr (.success
        (FollowerDownMeasurability.followerStateCode rate (states i))
        (FollowerLifecycleMeasurability.localMemoryCode (memories i))) := by
  obtain ⟨record, hrecordMem, htime, selected, hselected, hi⟩ := hsupport
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [] := by
    intro hnil
    simp [rawHRecords, hnil] at hrecordMem
  rcases rawH_endpoint_cases rate rewards C_star C_h z hK with hnil | hendpoint
  · rw [hnil.1] at hrecordMem
    cases hrecordMem
  · rcases hendpoint with ⟨b, _, hlater, _, _, _, _, _, hrecords⟩
    let H := actualHandoverRecords rate rewards C_star C_h z b
    have hmemH : record ∈ H := by
      change record ∈ (R[b.val] ::
        ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)).takeWhile
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
      rw [← hrecords]
      exact hrecordMem
    obtain ⟨jn, hjn, hrecordEq⟩ := List.mem_iff_getElem.mp hmemH
    let j : Fin H.length := ⟨jn, hjn⟩
    have hrecordEq' : H[j.val] = record := by simpa only [j] using hrecordEq
    subst record
    have hlookup : actualRecord rate rewards C_star C_h t z = some H[j.val] := by
      rw [← htime]
      exact actualHandover_lookup rate rewards C_star C_h z b j
    obtain ⟨payload, _, hframes⟩ := actual_later_handover_snapshot
      (rate := rate) rewards C_star C_h z b hlater
    obtain ⟨selectedFrame, states, memories, hselFrame, hpayload,
      hprepared, _, hfields, hnotReleased, _⟩ := hframes j
    have hselEq := Option.some.inj (hselFrame.symm.trans hselected)
    subst selectedFrame
    obtain ⟨_, _, _, _, _, _, _, hdecodeFrames⟩ :=
      actual_later_handover_decoder_correspondence
        (rate := rate) rewards C_star C_h z b hlater i
    obtain ⟨_, _, _, inputState, inputMemory, _, _, _, hinput, _⟩ := hdecodeFrames j
    obtain ⟨choice, hchoice, hcode⟩ :=
      ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_actual_choice
        rate rewards C_star C_h t i z H[j.val] inputState inputMemory hlookup hinput
    have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((hprepared i).symm.trans hchoice)
    refine ⟨H[j.val], selected, states, memories, hlookup, hselected, hi,
      hprepared, ?_, hnotReleased, ?_⟩
    · intro k hk
      rw [hpayload]
      exact hfields k hk
    · change ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
        rate rewards C_star C_h t i z = _
      rw [hcode, ← heq.1, ← heq.2]

private theorem actual_record_fields (t : Fin p.T) (z : Source p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : actualLaunchBy rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hz.1
    have hrec := actualRecord_on_launch rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t z hz] at hr
    cases hr

private theorem startCode_status_eq (t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hcode : startCode rate rewards C_star C_h t i z = .inr (.success
      (FollowerDownMeasurability.followerStateCode rate state)
      (FollowerLifecycleMeasurability.localMemoryCode memory)))
    (s : Fin 3)
    (hstage : ∃ code memoryCode,
      startCode rate rewards C_star C_h t i z = .inr (.success code memoryCode) ∧
        code.status = s) :
    FollowerDownMeasurability.followerStatusCode state.status = s := by
  obtain ⟨code, memoryCode, hcode', hstatus⟩ := hstage
  have heq := Sum.inr.inj (hcode.symm.trans hcode')
  cases heq
  exact hstatus

/-- On a genuine supported H task the before-stage physical observation has
exactly the DOWN one-bit collision geometry. No action identity is assumed. -/
theorem before_physical_service (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source p)
    (hz : z ∈ A_before rate rewards C_star C_h t i) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection record.input),
      actualRecord rate rewards C_star C_h t z = some record ∧
      record.output.preparation.coordinator.selection = some selected ∧
      (V_before rate rewards C_star C_h i t z ↔
        PublicDiscreteDraws.slotDraw (record.input.row.2 t).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 t).1 = i ∧
        CoordinatorLocalArmChoice.currentDownHash selected.view.payload
          (record.input.row.2 t) i = 1 ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (record.input.row.2 t).1).val (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val) := by
  obtain ⟨record, selected, states, memories, hr, hs, hi, hc, hf, hn, hcode⟩ :=
    actual_task_frame rate rewards C_star C_h t i z hz.1
  obtain ⟨_, _, htime, hreward⟩ := actual_record_fields rate rewards C_star C_h t z record hr
  have hstatusCode := startCode_status_eq rate rewards C_star C_h t i z
    (states i) (memories i) hcode 0 hz.2
  have hu : (states i).status = .unoccupied := by
    cases hstatus : (states i).status <;>
      simp_all [FollowerDownMeasurability.followerStatusCode]
  refine ⟨record, selected, hr, hs, ?_⟩
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hfeedback (hdown : PublicDiscreteDraws.slotDraw (record.input.row.2 t).1 =
      PublicDiscreteDraws.downSlot)
      (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (record.input.row.2 t).1 = i) :
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val =
      if CoordinatorLocalArmChoice.currentDownHash selected.view.payload
          (record.input.row.2 t) i = 1 then
        ((rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (record.input.row.2 t).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val : ℝ) / (D p : ℝ)
      else 0 := by
    let snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment :=
      ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
    let input := handoverRoundInput selected.view.payload record.input.row record.input.time
    have ha := actual_handover_down_actions record.input selected
      (by rw [← hprep]; exact hs) states memories
      (by intro j; rw [← hprep]; exact hc j) hf hn i hi
      (by rw [htime]; exact hdown) (by rw [htime]; exact hdraw)
    have ha' : record.output.preparation.arms.actions =
        ActiveRoundActions.actions p.two_le_m snapshot input := by
      rw [hprep]
      exact ha
    have hinv : ActiveRoundActions.no_released_while_missing snapshot := by
      intro _ j
      exact hn j
    have hselected : input.selected = i := by
      dsimp [input, handoverRoundInput]
      rw [htime]
      exact hdraw
    have hbit : input.down.bit = CoordinatorLocalArmChoice.currentDownHash
        selected.view.payload (record.input.row.2 t) i := by
      rw [handoverRoundInput_down_bit]
      rw [htime, hdraw]
    calc
      _ = ActiveRoundActions.feedback p.two_le_m snapshot input
          (handoverWholeRewardRow record) (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
        calc
          _ = FiniteBanditModel.playerFeedback record.output.preparation.arms.actions
              (fun a => ((record.input.rewards record.input.time a).val : ℝ) / (D p : ℝ))
              (PublicDiscreteDraws.followerPlayer p.two_le_m i) :=
            record.output.preparation.feedback.feedback_scalar_eq_playerFeedback _
          _ = _ := by rw [ha']; rfl
      _ = _ := by
        have h := ActiveRoundActions.unoccupied_down_feedback p.two_le_m snapshot input
          (handoverWholeRewardRow record)
          (by dsimp [input, handoverRoundInput]; rw [htime]; exact hdown)
          (by rw [hselected]; exact hi) hinv (by rw [hselected]; exact hu)
        rw [hselected] at h
        rw [h, hbit]
        dsimp [handoverWholeRewardRow, handoverWholeRewardRowAt,
          RealRewardGridCount.realRewardGridValue, input, handoverRoundInput]
        rw [htime, hreward]
  have hpositive (a : Fin p.K) :
      0 < ((rewards t a).val : ℝ) / (D p : ℝ) ↔ 0 < (rewards t a).val := by
    have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
    rw [div_pos_iff_of_pos_right hD]
    exact_mod_cast Iff.rfl
  constructor
  · rintro ⟨other, hother, hdown, hdraw, hpos⟩
    have heq := Option.some.inj (hother.symm.trans hr)
    subst other
    rw [htime] at hdown hdraw
    refine ⟨hdown, hdraw, ?_⟩
    rw [hfeedback hdown hdraw] at hpos
    split_ifs at hpos with hbit
    · exact ⟨hbit, (hpositive _).mp hpos⟩
    · exact False.elim (lt_irrefl 0 hpos)
  · rintro ⟨hdown, hdraw, hbit, hpos⟩
    refine ⟨record, hr, ?_, ?_, ?_⟩
    · rw [htime]
      exact hdown
    · rw [htime]
      exact hdraw
    · rw [hfeedback hdown hdraw, ite_eq_left hbit]
      exact (hpositive _).mpr hpos

/-- On a genuine supported H task, the pending-stage zero-bit observation
at the coordinator is exactly the selected receiver's whole-row reward. -/
theorem after_physical_service (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source p)
    (hz : z ∈ A_after rate rewards C_star C_h t i) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection record.input),
      actualRecord rate rewards C_star C_h t z = some record ∧
      record.output.preparation.coordinator.selection = some selected ∧
      (V_after rate rewards C_star C_h i t z ↔
        PublicDiscreteDraws.slotDraw (record.input.row.2 t).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 t).1 = i ∧
        CoordinatorLocalArmChoice.currentDownHash selected.view.payload
          (record.input.row.2 t) i = 0 ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (record.input.row.2 t).1).val (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val) := by
  obtain ⟨record, selected, states, memories, hr, hs, hi, hc, hf, hn, hcode⟩ :=
    actual_task_frame rate rewards C_star C_h t i z hz.1
  obtain ⟨_, _, htime, hreward⟩ := actual_record_fields rate rewards C_star C_h t z record hr
  have hstatusCode := startCode_status_eq rate rewards C_star C_h t i z
    (states i) (memories i) hcode 1 hz.2
  have hpending : (states i).status = .pending := by
    cases hstatus : (states i).status <;>
      simp_all [FollowerDownMeasurability.followerStatusCode]
  refine ⟨record, selected, hr, hs, ?_⟩
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hfeedback (hdown : PublicDiscreteDraws.slotDraw (record.input.row.2 t).1 =
      PublicDiscreteDraws.downSlot)
      (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (record.input.row.2 t).1 = i)
      (hzero : CoordinatorLocalArmChoice.currentDownHash selected.view.payload
        (record.input.row.2 t) i = 0) :
      (record.output.preparation.feedback.observations
        (ActiveRoundActions.coordinator p.two_le_m)).val.val =
        ((rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (record.input.row.2 t).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val : ℝ) / (D p : ℝ) := by
    let snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment :=
      ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
    let input := handoverRoundInput selected.view.payload record.input.row record.input.time
    have ha := actual_handover_down_actions record.input selected
      (by rw [← hprep]; exact hs) states memories
      (by intro j; rw [← hprep]; exact hc j) hf hn i hi
      (by rw [htime]; exact hdown) (by rw [htime]; exact hdraw)
    have ha' : record.output.preparation.arms.actions =
        ActiveRoundActions.actions p.two_le_m snapshot input := by
      rw [hprep]
      exact ha
    have hinv : ActiveRoundActions.no_released_while_missing snapshot := by
      intro _ j
      exact hn j
    have hselected : input.selected = i := by
      dsimp [input, handoverRoundInput]
      rw [htime]
      exact hdraw
    have hbit : input.down.bit = 0 := by
      rw [handoverRoundInput_down_bit, htime, hdraw]
      exact hzero
    calc
      _ = FiniteBanditModel.playerFeedback record.output.preparation.arms.actions
          (fun a => ((record.input.rewards record.input.time a).val : ℝ) / (D p : ℝ))
          (ActiveRoundActions.coordinator p.two_le_m) :=
        record.output.preparation.feedback.feedback_scalar_eq_playerFeedback _
      _ = ActiveRoundActions.feedback p.two_le_m snapshot input
          (handoverWholeRewardRow record) (ActiveRoundActions.coordinator p.two_le_m) := by
        rw [ha']
        rfl
      _ = _ := by
        rw [ActiveRoundActions.pending_down_coordinator_feedback p.two_le_m snapshot input
          (handoverWholeRewardRow record)
          (by dsimp [input, handoverRoundInput]; rw [htime]; exact hdown)
          (by rw [hselected]; exact hi) hinv
          (by rw [hselected]; exact hpending) hbit, hselected]
        dsimp [handoverWholeRewardRow, handoverWholeRewardRowAt,
          RealRewardGridCount.realRewardGridValue, input, handoverRoundInput]
        rw [htime, hreward]
  have hpositive (a : Fin p.K) :
      0 < ((rewards t a).val : ℝ) / (D p : ℝ) ↔ 0 < (rewards t a).val := by
    have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
    rw [div_pos_iff_of_pos_right hD]
    exact_mod_cast Iff.rfl
  constructor
  · rintro ⟨other, otherSelection, hother, hotherSelection, hdown, hdraw, hzero, hpos⟩
    have heq := Option.some.inj (hother.symm.trans hr)
    subst other
    have hselEq := Option.some.inj (hotherSelection.symm.trans hs)
    subst otherSelection
    rw [htime] at hdown hdraw hzero
    rw [hfeedback hdown hdraw hzero] at hpos
    exact ⟨hdown, hdraw, hzero, (hpositive _).mp hpos⟩
  · rintro ⟨hdown, hdraw, hzero, hpos⟩
    refine ⟨record, selected, hr, hs, ?_, ?_, ?_, ?_⟩
    · rw [htime]
      exact hdown
    · rw [htime]
      exact hdraw
    · rw [htime]
      exact hzero
    · rw [hfeedback hdown hdraw hzero]
      exact (hpositive _).mpr hpos

/-- Erasing from the current date removes any replacement of its whole
current control, while retaining all private coordinates and other rows. -/
theorem sourcePrefix_replace (t : Fin p.T) (z : Source p) (u : TimeControl p) :
    sourcePrefix control0 t.val (replaceSourceControl p t z u) =
      sourcePrefix control0 t.val z := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext j
    by_cases hj : j = ActualInitializationPhysicalStep.selectedRowIndex p z
    · subst j
      simp only [sourcePrefix, replaceSourceControl, sourceCoordinatorIndex_eq_selectedRowIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < t.val
      · have hvt : v ≠ t := fun h => by subst v; omega
        simp only [hv, ite_true, Function.update_of_ne hvt]
      · simp only [hv, ite_false]
    · have hj' : j ≠ ActualInitializationPhysicalStep.selectedRowIndex p
          (replaceSourceControl p t z u) := hj
      rw [sourcePrefix_otherRow control0 _ _ j hj', sourcePrefix_otherRow control0 _ _ j hj]
      exact Function.update_of_ne hj _ _
  · rfl

include control0 in
/-- Every whole current-control replacement has the same literal before stage. -/
theorem A_before_replace (t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source p) (u : TimeControl p) :
    replaceSourceControl p t z u ∈ A_before rate rewards C_star C_h t i ↔
      z ∈ A_before rate rewards C_star C_h t i := by
  rw [A_before_factor rate rewards C_star C_h control0,
    sourcePrefix_replace control0,
    ← A_before_factor rate rewards C_star C_h control0]

include control0 in
/-- Every whole current-control replacement has the same literal after stage. -/
theorem A_after_replace (t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source p) (u : TimeControl p) :
    replaceSourceControl p t z u ∈ A_after rate rewards C_star C_h t i ↔
      z ∈ A_after rate rewards C_star C_h t i := by
  rw [A_after_factor rate rewards C_star C_h control0,
    sourcePrefix_replace control0,
    ← A_after_factor rate rewards C_star C_h control0]

private theorem actual_record_index (t : Fin p.T) (z : Source p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r) :
    ∃ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val] = r := by
  unfold actualRecord at hr
  split_ifs at hr with hstart
  · obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp hr
    exact ⟨⟨_, hk⟩, heq⟩

/-- At an actual empty collection, the selected payload is the output of the
actual later-start operation. Both sides of the freeze boundary are included. -/
private theorem actual_collection_payload (t : Fin p.T) (z : Source p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : r.input.state.coordinator = .collection P l saved) (hempty : l.pending = ∅)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some selected) :
    ∃ u : Fin p.T, u.val + 1 = l.cutoff ∧
      let input := ReferenceActivePhysicalStep.collectionInput r.input P l
        (ReferenceActivePhysicalStep.collectionClock P l saved u) u
      ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input)
        (started : CoordinatorPhaseClock.StartRoundResult p),
        CoordinatorPhaseClock.startRound p rate.eta.val r.input.time input.clock l.pending =
          .ok started ∧
        ∃ instruction : CoordinatorPhaseClock.AssignmentStartInstruction p,
          started.assignmentStart = some instruction ∧ instruction.time = r.input.time ∧
          let operation := CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq
          ∃ (consistent : LaterAssignmentStartOperation.LocalConsistency P operation)
            (output : LaterAssignmentStartOperation.SuccessfulStart P operation instruction r.input.row)
            (hlocal : output.localConsistency = consistent),
            LaterAssignmentStartOperation.laterAssignmentStart P operation instruction r.input.row
              consistent = .success output hlocal ∧ selected.view.payload = output.payload := by
  obtain ⟨k, hk⟩ := actual_record_index rate rewards C_star C_h t z r hr
  subst r
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hstate' : R[k.val].input.state.coordinator = .collection P l saved := hstate
  have hsel' : R[k.val].output.preparation.coordinator.selection = some selected := by
    exact hsel
  by_cases hbefore : R[k.val].input.time.val + 1 < l.freezeAt
  · obtain ⟨u, hu, core, started, hstart, instruction, hassignment,
      htime, _hkind, _hsigma, _hcutoff, consistent, output, hlocal,
      hcall, _clockData, _installed, _arm, _hprior, _hresult, _hpending,
      _hinstall, _hdispatch, _hscore, _hqueue, _hprevious, _hbase,
      _henvelope, hpayload, _hanchor, _hlawAnchor, _hcutoffRegisters,
      _hcurrentRegisters, _hsourceScore, _hinitialQueue, _hqueues,
      _hvector, actualSelected, _hselection, houtputSelection, hselectedPayload, _⟩ :=
      ReferenceCompleteEmptyCorrectedCoordinatorStep.complete_empty_corrected_coordinator_step
        rewards C_star C_h z k P l saved hstate' hempty hbefore
    have hselectedEq := Option.some.inj (houtputSelection.symm.trans hsel')
    subst actualSelected
    refine ⟨u, hu, ?_⟩
    exact
      ⟨core, started, hstart, instruction, hassignment, htime,
        consistent, output, hlocal, hcall, hselectedPayload.trans hpayload⟩
  · obtain ⟨u, hu, core, _hscore, started, hstart, instruction,
      hassignment, htime, _hkind, output, hlocal, hcall, _hsource,
      _hinitial, _hweight, _hanchor, _hqueues, _hdomains, _hbase,
      _hclock, _mass, _sampled, _hmass, _hsampled, _hvector, _arm,
      _hdispatch, _hprepared, actualSelected, _hselection, hpayload,
      _hcutoff, _hlive, houtputSelection, _⟩ :=
      ReferenceCompleteEmptyRenewalCoordinatorStep.complete_empty_renewal_coordinator_step
        rate rewards C_star C_h z k P l saved hstate' hempty
          (Nat.le_of_not_gt hbefore)
    have hselectedEq := Option.some.inj (houtputSelection.symm.trans hsel')
    subst actualSelected
    refine ⟨u, hu, ?_⟩
    exact
      ⟨core, started, hstart, instruction, hassignment, htime,
        _, output, hlocal, hcall, hpayload⟩

private theorem localConsistency_eq {P : ReferenceActivePhysicalStep.Payload rate}
    {l : LaterAssignmentStartOperation.LocalLedger P}
    (a b : LaterAssignmentStartOperation.LocalConsistency P l) : a = b := by
  have hfreeze : a.oldFreezeAt = b.oldFreezeAt :=
    a.oldFreezeAt_eq.trans b.oldFreezeAt_eq.symm
  cases a
  cases b
  cases hfreeze
  rfl

/-- Startup locality uses the whole current assignment vector. The payload
can vary with that vector; only the affine family is erased here. -/
private theorem collection_payload_eq_of_scalar (t : Fin p.T) (z z' : Source p)
    (r r' : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r)
    (hr' : actualRecord rate rewards C_star C_h t z' = some r')
    (P : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hc : r.input.state.coordinator = .collection P l saved)
    (hc' : r'.input.state.coordinator = .collection P l saved) (hempty : l.pending = ∅)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (selected' : ReferenceActivePhysicalStep.Selection r'.input)
    (hs : r.output.preparation.coordinator.selection = some selected)
    (hs' : r'.output.preparation.coordinator.selection = some selected')
    (hscalar : (r.input.row.2 r.input.time).1 = (r'.input.row.2 r'.input.time).1) :
    selected.view.payload = selected'.view.payload := by
  obtain ⟨u, hu, core, started, hstart, instruction, hi, htime,
    consistent, output, hlocal, hcall, hpayload⟩ :=
    actual_collection_payload rate rewards C_star C_h t z r hr P l saved hc hempty selected hs
  obtain ⟨u', hu', core', started', hstart', instruction', hi', htime',
    consistent', output', hlocal', hcall', hpayload'⟩ :=
    actual_collection_payload rate rewards C_star C_h t z' r' hr' P l saved hc' hempty selected' hs'
  have huEq : u = u' := by apply Fin.ext; omega
  subst u'
  have hdate : r.input.time = r'.input.time :=
    (actual_record_fields rate rewards C_star C_h t z r hr).2.2.1.trans
      (actual_record_fields rate rewards C_star C_h t z' r' hr').2.2.1.symm
  have hstarted : started = started' := by
    apply Except.ok.inj
    change CoordinatorPhaseClock.startRound p rate.eta.val r.input.time
      (ReferenceActivePhysicalStep.collectionClock P l saved u) l.pending = .ok started at hstart
    change CoordinatorPhaseClock.startRound p rate.eta.val r'.input.time
      (ReferenceActivePhysicalStep.collectionClock P l saved u) l.pending = .ok started' at hstart'
    rw [hdate] at hstart
    exact hstart.symm.trans hstart'
  subst started'
  have hinstruction : instruction = instruction' := Option.some.inj (hi.symm.trans hi')
  subst instruction'
  have hconsistent : consistent = consistent' := localConsistency_eq rate consistent consistent'
  have hlocal'' : output'.localConsistency = consistent := hlocal'.trans hconsistent.symm
  have hcall'' : LaterAssignmentStartOperation.laterAssignmentStart P
      (CoordinatorRoundDispatch.collectionOperationLedger
        (ReferenceActivePhysicalStep.collectionInput r.input P l
          (ReferenceActivePhysicalStep.collectionClock P l saved u) u) core.payload_n_eq)
      instruction r'.input.row consistent = .success output' hlocal'' := by
    cases hconsistent
    exact hcall'
  have hvector : LaterAssignmentStartOperation.ownAssignmentVector r.input.row instruction.time =
      LaterAssignmentStartOperation.ownAssignmentVector r'.input.row instruction.time := by
    calc
      _ = ContinuousControlSlice.assignmentVector (r.input.row.2 r.input.time).1 := by
        rw [htime]
        rfl
      _ = ContinuousControlSlice.assignmentVector (r'.input.row.2 r'.input.time).1 :=
        congrArg ContinuousControlSlice.assignmentVector hscalar
      _ = _ := by rw [htime']; rfl
  have h := LaterAssignmentStartMeasurability.laterAssignmentStart_payload?_eq_of_ownAssignmentVector_eq
    P ⟨_, instruction, consistent⟩ r.input.row r'.input.row hvector
  rw [hcall, hcall''] at h
  change some output.payload = some output'.payload at h
  exact hpayload.trans ((Option.some.inj h).trans hpayload'.symm)

private theorem live_selection_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (hc : x.state.coordinator = .live registers owned base)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hsel : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected) :
    selected.view.payload = registers.payload := by
  change (ReferenceActivePhysicalStep.dispatch x).selection = some selected at hsel
  have hd : ReferenceActivePhysicalStep.dispatch x = .live registers owned base
      (CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x registers owned base)) := by
    simp only [ReferenceActivePhysicalStep.dispatch, hc, CoordinatorRoundDispatch.dispatch]
    rfl
  rw [hd] at hsel
  cases hout : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput x registers owned base) <;>
    simp only [hout, ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, dite_true] at hsel
  all_goals first
    | cases hsel
      rfl
    | contradiction

private theorem support_incoming_ne_false (t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source p) (hsupport : rawHTaskSupport rate rewards C_star C_h t i z) :
    handoverIncomingData rate rewards C_star C_h t z ≠ some (false, none) := by
  intro hdata
  have hquery := (rawHTaskSupport_iff_handoverPreRoundTask
    rate rewards C_star C_h z t i).mp hsupport
  unfold handoverPreRoundObservable at hquery
  rw [hdata] at hquery
  cases hphase : handoverPhaseBefore rate rewards C_star C_h t z <;>
    simp only [hphase, handoverPreRoundTask, Bool.false_eq_true] at hquery

include control0 in
/-- The actual selected payload on a supported later H section is independent
of the current affine family at a fixed scalar slice. Startup and continuing
use the same original run, with no fixed first-live payload. -/
theorem replacement_payload_eq_of_same_slice (t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source p) (hz : rawHTaskSupport rate rewards C_star C_h t i z)
    (u v : TimeControl p) (huv : u.1 = v.1)
    (r r' : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (selected' : ReferenceActivePhysicalStep.Selection r'.input)
    (hr : actualRecord rate rewards C_star C_h t (replaceSourceControl p t z u) = some r)
    (hr' : actualRecord rate rewards C_star C_h t (replaceSourceControl p t z v) = some r')
    (hs : r.output.preparation.coordinator.selection = some selected)
    (hs' : r'.output.preparation.coordinator.selection = some selected') :
    selected.view.payload = selected'.view.payload := by
  have hsupport : rawHTaskSupport rate rewards C_star C_h t i
      (replaceSourceControl p t z u) := by
    rw [rawHTaskSupport_factor rate rewards C_star C_h control0,
      sourcePrefix_replace control0,
      ← rawHTaskSupport_factor rate rewards C_star C_h control0]
    exact hz
  have hnotFalse := support_incoming_ne_false rate rewards C_star C_h t i _ hsupport
  have hin : incoming rate rewards C_star C_h t (replaceSourceControl p t z u) =
      incoming rate rewards C_star C_h t (replaceSourceControl p t z v) := by
    rw [incoming_factor rate rewards C_star C_h control0,
      incoming_factor rate rewards C_star C_h control0 t (replaceSourceControl p t z v),
      sourcePrefix_replace control0, sourcePrefix_replace control0]
  simp only [incoming, hr, hr', Option.map_some, Option.some.injEq] at hin
  have hstate := ReferenceActivePhysicalStepMeasurability.encodeState_injective hin
  obtain ⟨hrows, hJ, ht, _⟩ := actual_record_fields rate rewards C_star C_h t _ r hr
  obtain ⟨hrows', hJ', ht', _⟩ := actual_record_fields rate rewards C_star C_h t _ r' hr'
  have hscalar : (r.input.row.2 r.input.time).1 = (r'.input.row.2 r'.input.time).1 := by
    simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hJ, ht,
      hrows', hJ', ht', replaceSourceControl, ActualInitializationPhysicalStep.selectedRowIndex,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, Function.update_self]
    exact huv
  have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hprep' : r'.output.preparation = ReferenceActivePhysicalStep.prepare r'.input := by
    rw [r'.output_eq]
    rfl
  cases hc : r.input.state.coordinator with
  | first =>
      apply False.elim
      apply hnotFalse
      simp only [handoverIncomingData, incoming, hr, Option.map_some,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, incomingHandoverData]
  | live registers owned base =>
      have hc' : r'.input.state.coordinator = .live registers owned base := hstate ▸ hc
      rw [live_selection_payload rate r.input registers owned base hc selected
        (by rw [← hprep]; exact hs),
        live_selection_payload rate r'.input registers owned base hc' selected'
          (by rw [← hprep']; exact hs')]
  | collection P l saved =>
      have hc' : r'.input.state.coordinator = .collection P l saved := hstate ▸ hc
      have hempty : l.pending = ∅ := by
        by_contra hnonempty
        apply hnotFalse
        simp only [handoverIncomingData, incoming, hr, Option.map_some,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, incomingHandoverData,
          hnonempty, decide_false]
      exact collection_payload_eq_of_scalar rate rewards C_star C_h t _ _ r r' hr hr'
        P l saved hc hc' hempty selected selected' hs hs' hscalar
  | dagger =>
      rw [hprep] at hs
      change (ReferenceActivePhysicalStep.dispatch r.input).selection = some selected at hs
      rw [ReferenceActivePhysicalStep.dispatch_dagger r.input hc] at hs
      cases hs

private def stageSet (accepted : Bool) (t : Fin p.T) (i : Fin (p.m - 1)) :=
  if accepted then A_after rate rewards C_star C_h t i else A_before rate rewards C_star C_h t i

private def serviceEvent (accepted : Bool) (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source p) :=
  if accepted then V_after rate rewards C_star C_h i t z else V_before rate rewards C_star C_h i t z

include control0 in
private theorem stageSet_replace (accepted : Bool) (t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source p) (u : TimeControl p) :
    replaceSourceControl p t z u ∈ stageSet rate rewards C_star C_h accepted t i ↔
      z ∈ stageSet rate rewards C_star C_h accepted t i := by
  cases accepted
  · exact A_before_replace rate rewards C_star C_h control0 t i z u
  · exact A_after_replace rate rewards C_star C_h control0 t i z u

private theorem stage_physical_service (accepted : Bool) (t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source p) (hz : z ∈ stageSet rate rewards C_star C_h accepted t i) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection record.input),
      actualRecord rate rewards C_star C_h t z = some record ∧
      record.output.preparation.coordinator.selection = some selected ∧
      (serviceEvent rate rewards C_star C_h accepted t i z ↔
        PublicDiscreteDraws.slotDraw (record.input.row.2 t).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 t).1 = i ∧
        CoordinatorLocalArmChoice.currentDownHash selected.view.payload
          (record.input.row.2 t) i = (if accepted then 0 else 1) ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (record.input.row.2 t).1).val (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val) := by
  cases accepted
  · exact before_physical_service rate rewards C_star C_h t i z hz
  · exact after_physical_service rate rewards C_star C_h t i z hz

private theorem replacement_service_integrable (accepted : Bool)
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source p) :
    Integrable (fun u : TimeControl p =>
      if serviceEvent rate rewards C_star C_h accepted t i (replaceSourceControl p t z u)
      then (1 : ℝ) else 0) (timeControlLaw p) := by
  cases accepted
  · have hset := (measurableSet_B_before rate rewards C_star C_h i t).preimage
      ((measurable_const (a := z)).prodMk measurable_id)
    exact (integrable_const (1 : ℝ)).indicator hset
  · exact integrable_replacement_observation rate rewards C_star C_h i t z

private theorem affine_bit_integral (i : Fin (d p))
    (word : AffineChannelLaw.Word (B p)) (bit : AffineChannelLaw.Bit) :
    (∫ a : AffineSamples p,
      (if AffineChannelLaw.affineHash (a (0, i)) word = bit then (1 : ℝ) else 0)
      ∂affineSamplesLaw p) = 1 / 2 := by
  let A : Set (AffineChannelLaw.Sample (B p)) :=
    {sample | AffineChannelLaw.affineHash sample word = bit}
  have hA : MeasurableSet A := MeasurableSet.of_discrete
  have hpre : MeasurableSet {a : AffineSamples p |
      AffineChannelLaw.affineHash (a (0, i)) word = bit} :=
    hA.preimage (measurable_pi_apply (0, i))
  have hmass : (affineSamplesLaw p)
      {a : AffineSamples p | AffineChannelLaw.affineHash (a (0, i)) word = bit} =
      (1 : ℝ≥0∞) / 2 := by
    change (affineSamplesLaw p) ((fun a : AffineSamples p => a (0, i)) ⁻¹' A) = _
    rw [← Measure.map_apply (measurable_pi_apply (0, i)) hA]
    have hmap := (measurePreserving_eval
      (fun _ : Channel p => (AffineChannelLaw.jointLaw (B p)).toMeasure) (0, i)).map_eq
    change (Measure.map _ (Measure.pi _)) A = _
    rw [hmap, ← AffineChannelLaw.eventProbability_eq_measure,
      AffineChannelLaw.affineHash_probability]
  have hint : (∫ a : AffineSamples p,
      ({a : AffineSamples p | AffineChannelLaw.affineHash (a (0, i)) word = bit}.indicator
        (fun _ => (1 : ℝ))) a ∂affineSamplesLaw p) =
      (affineSamplesLaw p).real {a : AffineSamples p |
        AffineChannelLaw.affineHash (a (0, i)) word = bit} := integral_indicator_one hpre
  simp only [Set.indicator_apply, Set.mem_ofPred_eq] at hint
  rw [hint, Measure.real, hmass]
  norm_num

private theorem actual_record_replaced_current (t : Fin p.T) (z : Source p)
    (u : TimeControl p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t (replaceSourceControl p t z u) = some r) :
    r.input.row.2 t = u := by
  obtain ⟨hrows, hJ, _, _⟩ := actual_record_fields rate rewards C_star C_h t _ r hr
  simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hJ,
    replaceSourceControl, ActualInitializationPhysicalStep.selectedRowIndex,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, Function.update_self]

include control0 in
private theorem actual_affine_first_integral (accepted : Bool) (t : Fin p.T)
    (i : Fin (p.m - 1)) (z : Source p)
    (hz : z ∈ stageSet rate rewards C_star C_h accepted t i) (x : Slice p) :
    (∫ a : AffineSamples p,
      (if serviceEvent rate rewards C_star C_h accepted t i (replaceSourceControl p t z (x, a))
       then (1 : ℝ) else 0) ∂affineSamplesLaw p) =
      (if PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val
       then (1 : ℝ) else 0) * (1 / 2) := by
  classical
  have hsupport : rawHTaskSupport rate rewards C_star C_h t i z := by
    cases accepted
    · exact hz.1
    · exact hz.1
  have hstage (a : AffineSamples p) :=
    (stageSet_replace rate rewards C_star C_h control0 accepted t i z (x, a)).mpr hz
  obtain ⟨r0, selected0, hr0, hs0, _⟩ := stage_physical_service
    rate rewards C_star C_h accepted t i _ (hstage control0.2)
  let word := CoordinatorLocalArmChoice.storedDownFlatWord selected0.view.payload i
  have heq (a : AffineSamples p) :
      (if serviceEvent rate rewards C_star C_h accepted t i (replaceSourceControl p t z (x, a))
       then (1 : ℝ) else 0) =
      (if PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val
       then (if AffineChannelLaw.affineHash (a (0, i)) word =
          (if accepted then 0 else 1) then 1 else 0)
       else 0) := by
    obtain ⟨r, selected, hr, hs, hgeometry⟩ := stage_physical_service
      rate rewards C_star C_h accepted t i _ (hstage a)
    have hpayload := replacement_payload_eq_of_same_slice rate rewards C_star C_h control0
      t i z hsupport (x, a) (x, control0.2) rfl r r0 selected selected0 hr hr0 hs hs0
    have hcurrent := actual_record_replaced_current rate rewards C_star C_h t z (x, a) r hr
    rw [hgeometry, hcurrent, hpayload]
    by_cases hbit : AffineChannelLaw.affineHash (a (0, i)) word =
        (if accepted then 0 else 1) <;>
      simp only [CoordinatorLocalArmChoice.currentDownHash,
        CoordinatorLocalArmChoice.downChannel, word] at hbit ⊢ <;>
      simp only [hbit, and_false, true_and, false_and, ite_true, ite_false, ite_self]
  simp_rw [heq]
  by_cases hscalar : PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
      0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val
  · simp_rw [ite_eq_left hscalar]
    simpa only [one_mul] using affine_bit_integral i word (if accepted then 0 else 1)
  · simp_rw [ite_eq_right hscalar]
    simp only [integral_zero, zero_mul]

include control0 in
private theorem actual_replacement_integral (accepted : Bool) (t : Fin p.T)
    (i : Fin (p.m - 1)) (z : Source p)
    (hz : z ∈ stageSet rate rewards C_star C_h accepted t i) :
    (∫ u : TimeControl p,
      (if serviceEvent rate rewards C_star C_h accepted t i (replaceSourceControl p t z u)
       then (1 : ℝ) else 0) ∂timeControlLaw p) = serviceCoefficient rewards t := by
  classical
  let A : Set (Slice p) := {x |
    PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
      0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val}
  have hA : MeasurableSet A :=
    ((PublicDiscreteDraws.measurable_slotDraw (m := p.m) (K := p.K))
      (measurableSet_singleton _)).inter
      (((PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K)
        (measurableSet_singleton _)).inter
        ((MeasurableSet.of_discrete : MeasurableSet
          {tuple : OrderedTupleSampler.Tuple p.m p.K |
            0 < (rewards t (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val}).preimage
          (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K)))
  have hpositive (a : Fin p.K) :
      0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a) ↔
        0 < (rewards t a).val := by
    change 0 < ((rewards t a).val : ℝ) / (D p : ℝ) ↔ _
    have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
    rw [div_pos_iff_of_pos_right hD]
    exact_mod_cast Iff.rfl
  have hmass : (ContinuousControlSlice.sliceLaw p.m p.K) A * ((1 : ENNReal) / 2) =
      ENNReal.ofReal (serviceCoefficient rewards t) := by
    have h := positive_receiver_slice_half_probability rewards t i
    dsimp only at h
    rw [positiveArms_card_eq_original_grid_count rewards t] at h
    have hAeq : {x : Slice p |
        PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)))} = A := by
      ext x
      simp only [A, Set.mem_ofPred_eq, hpositive]
    rw [hAeq] at h
    simpa only [serviceCoefficient, ContinuousLearningRows.d] using h
  have hnonneg : 0 ≤ serviceCoefficient rewards t := by
    unfold serviceCoefficient
    positivity
  have hreal : ((ContinuousControlSlice.sliceLaw p.m p.K) A).toReal * ((1 : ℝ) / 2) =
      serviceCoefficient rewards t := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hnonneg] using
      congrArg ENNReal.toReal hmass
  rw [timeControlLaw, integral_prod _
    (replacement_service_integrable rate rewards C_star C_h accepted t i z)]
  simp_rw [actual_affine_first_integral rate rewards C_star C_h control0 accepted t i z hz]
  have hindicator : (fun x : Slice p =>
      if PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val then (1 : ℝ) else 0) =
      A.indicator 1 := by
    funext x
    simp only [A, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  rw [integral_mul_const, hindicator, integral_indicator_one hA, Measure.real]
  exact hreal

include control0 in
/-- Both actual masked service indicators are integrable on the entire
original source law, including null and exceptional branches. -/
theorem integrable_service_indicators (t : Fin p.T) (i : Fin (p.m - 1)) :
    Integrable (X_before rate rewards C_star C_h t i) μ ∧
      Integrable (X_after rate rewards C_star C_h t i) μ := by
  classical
  have hb : MeasurableSet (A_before rate rewards C_star C_h t i) :=
    (sourcePrefixFiltration control0).le _ _
      (measurableSet_A_before rate rewards C_star C_h control0 t i)
  have ha : MeasurableSet (A_after rate rewards C_star C_h t i) :=
    (sourcePrefixFiltration control0).le _ _
      (measurableSet_A_after rate rewards C_star C_h control0 t i)
  constructor
  · have hint := (integrable_const (1 : ℝ) : Integrable (fun _ : Source p => (1 : ℝ)) μ).indicator
      (hb.inter (measurableSet_V_before rate rewards C_star C_h i t))
    convert hint using 1
    funext z
    by_cases hstage : z ∈ A_before rate rewards C_star C_h t i <;>
      by_cases hevent : V_before rate rewards C_star C_h i t z <;>
      simp only [X_before, Set.indicator_apply, Set.mem_inter_iff, Set.mem_ofPred_eq,
        hstage, hevent, and_self, and_false, false_and, ite_true, ite_false,
        one_mul, zero_mul]
  · have hint := (integrable_const (1 : ℝ) : Integrable (fun _ : Source p => (1 : ℝ)) μ).indicator
      (ha.inter (measurableSet_V_after rate rewards C_star C_h i t))
    convert hint using 1
    funext z
    by_cases hstage : z ∈ A_after rate rewards C_star C_h t i <;>
      by_cases hevent : V_after rate rewards C_star C_h i t z <;>
      simp only [X_after, Set.indicator_apply, Set.mem_inter_iff, Set.mem_ofPred_eq,
        hstage, hevent, and_self, and_false, false_and, ite_true, ite_false,
        one_mul, zero_mul]

/-- The original-source fresh service coefficient for the actual later H
handover, jointly before and after DOWN acceptance. All geometry and payload
locality are produced internally from the actual run. -/
theorem actual_handover_service_condExp (t : Fin p.T) (i : Fin (p.m - 1)) :
    (μ[(X_before rate rewards C_star C_h t i) | F (t.val + 1)] =ᵐ[μ]
      fun z => (if z ∈ A_before rate rewards C_star C_h t i then (1 : ℝ) else 0) *
        serviceCoefficient rewards t) ∧
    (μ[(X_after rate rewards C_star C_h t i) | F (t.val + 1)] =ᵐ[μ]
      fun z => (if z ∈ A_after rate rewards C_star C_h t i then (1 : ℝ) else 0) *
        serviceCoefficient rewards t) := by
  classical
  constructor
  · filter_upwards [before_condExp_integral rate rewards C_star C_h control0 t i] with z hz
    rw [hz]
    by_cases hstage : z ∈ A_before rate rewards C_star C_h t i
    · have hprefix := (A_before_factor rate rewards C_star C_h control0 t i z).mp hstage
      have hint := actual_replacement_integral rate rewards C_star C_h control0
        false t i (sourcePrefix control0 t.val z) hprefix
      simp only [serviceEvent, Bool.false_eq_true, ite_false] at hint
      rw [hint]
    · simp only [hstage, ite_false, zero_mul]
  · filter_upwards [after_condExp_integral rate rewards C_star C_h control0 t i] with z hz
    rw [hz]
    by_cases hstage : z ∈ A_after rate rewards C_star C_h t i
    · have hprefix := (A_after_factor rate rewards C_star C_h control0 t i z).mp hstage
      have hint := actual_replacement_integral rate rewards C_star C_h control0
        true t i (sourcePrefix control0 t.val z) hprefix
      simp only [serviceEvent, ite_true] at hint
      rw [hint]
    · simp only [hstage, ite_false, zero_mul]

/-- Disjoint actual stages make the mixed service a literal zero-one variable. -/
theorem service_zero_or_one (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source p) :
    X_before rate rewards C_star C_h t i z + X_after rate rewards C_star C_h t i z = 0 ∨
      X_before rate rewards C_star C_h t i z + X_after rate rewards C_star C_h t i z = 1 := by
  classical
  have hdisjoint := Set.disjoint_left.mp (A_before_disjoint_A_after rate rewards C_star C_h t i)
  by_cases hb : z ∈ A_before rate rewards C_star C_h t i
  · have ha : z ∉ A_after rate rewards C_star C_h t i := hdisjoint hb
    by_cases hv : V_before rate rewards C_star C_h i t z <;>
      simp only [X_before, X_after, hb, ha, hv, ite_true, ite_false,
        one_mul, zero_mul, add_zero, zero_ne_one, one_ne_zero, or_true, true_or]
  · by_cases ha : z ∈ A_after rate rewards C_star C_h t i <;>
      by_cases hv : V_after rate rewards C_star C_h i t z <;>
      simp only [X_before, X_after, hb, ha, hv, ite_true, ite_false,
        one_mul, zero_mul, zero_add, zero_ne_one, one_ne_zero, or_true, true_or]

/-- The combined actual later-H task service has the same instantaneous
coefficient on the whole raw H support. This asserts no phase quota or cost. -/
theorem combined_service_condExp (t : Fin p.T) (i : Fin (p.m - 1)) :
    μ[(fun z => X_before rate rewards C_star C_h t i z +
      X_after rate rewards C_star C_h t i z) | F (t.val + 1)] =ᵐ[μ]
      fun z => (if rawHTaskSupport rate rewards C_star C_h t i z then (1 : ℝ) else 0) *
        serviceCoefficient rewards t := by
  classical
  obtain ⟨hbInt, haInt⟩ := integrable_service_indicators rate rewards C_star C_h control0 t i
  obtain ⟨hbLaw, haLaw⟩ := actual_handover_service_condExp rate rewards C_star C_h control0 t i
  have hadd := condExp_add hbInt haInt (F (t.val + 1))
  filter_upwards [hadd, hbLaw, haLaw] with z hz hb ha
  change μ[(fun z => X_before rate rewards C_star C_h t i z +
      X_after rate rewards C_star C_h t i z) | F (t.val + 1)] z =
    μ[(X_before rate rewards C_star C_h t i) | F (t.val + 1)] z +
      μ[(X_after rate rewards C_star C_h t i) | F (t.val + 1)] z at hz
  rw [hz, hb, ha, ← add_mul]
  have hpartition : rawHTaskSupport rate rewards C_star C_h t i z ↔
      z ∈ A_before rate rewards C_star C_h t i ∨ z ∈ A_after rate rewards C_star C_h t i :=
    Set.ext_iff.mp (rawHTaskSupport_partition rate rewards C_star C_h t i) z
  have hmask : (if z ∈ A_before rate rewards C_star C_h t i then (1 : ℝ) else 0) +
      (if z ∈ A_after rate rewards C_star C_h t i then (1 : ℝ) else 0) =
      (if rawHTaskSupport rate rewards C_star C_h t i z then (1 : ℝ) else 0) := by
    by_cases hbSet : z ∈ A_before rate rewards C_star C_h t i
    · have haSet : z ∉ A_after rate rewards C_star C_h t i :=
        Set.disjoint_left.mp (A_before_disjoint_A_after rate rewards C_star C_h t i) hbSet
      simp only [hpartition, hbSet, haSet, true_or, ite_true, ite_false, add_zero]
    · by_cases haSet : z ∈ A_after rate rewards C_star C_h t i <;>
        simp only [hpartition, hbSet, haSet, false_or, ite_true, ite_false, zero_add]
  rw [hmask]

end Bandits.Support.ReferencePostReplacementCollectionHandoverFreshService

end

end
