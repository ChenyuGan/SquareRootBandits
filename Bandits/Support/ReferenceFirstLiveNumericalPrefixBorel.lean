/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceSavedMoments
public import Bandits.Support.ReferenceSourcePhysicalFlagConditionalLaw

import Lean.Elab.Tactic.Omega

/-!
# Ambient Borel numerical readout of the actual first-live count prefix

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264`,
`sources/zip4/manuscript/06_interruptions.tex:391-397,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

The readout below is taken from the actual first-live records on the original
source. It keeps absence distinct from every numerical cell and preserves the
ordinary product Borel spaces on all-arm reward and rate vectors. This ambient
measurability result is not a strict-past adaptation or a conditional law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstWindowNumericalStream

namespace Bandits.Support.ReferenceFirstLiveNumericalPrefixBorel

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val)

private abbrev SourceZ :=
  ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
    (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)

private abbrev ActiveRunInput (start : ℕ) :=
  ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start

private theorem sourceCrossing (z : SourceZ rate rewards C_star C_h q t s hs) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true :=
  z.property.2.1

private theorem sourceElapsed (z : SourceZ rate rewards C_star C_h q t s hs) :
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s :=
  z.property.2.2

private theorem sourceCountSpan (z : SourceZ rate rewards C_star C_h q t s hs) :
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed +
        (t.val - s) ≤ p.T := by
  rw [sourceElapsed rate rewards C_star C_h q t s hs z]
  omega

/-- A numerical cell after erasing its proof-only range certificates. -/
abbrev NumericalCellReadout (p : Parameters) :=
  Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ)))

/-- The exact finite numerical observation of the actual count-`n` first-live
source cells. A left tag means that the actual list has no entry at this
offset; it is never a fabricated zero cell. -/
def numericalCountPastReadout
    (control0 : TimeControl p)
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)) :
    Fin (t.val - s) → Unit ⊕ NumericalCellReadout p :=
  let _control0 := control0
  fun k =>
    match (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
      z.property.2.1 (t.val - s)
      (by
        have he : ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s :=
          by simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.property.2.2
        rw [he]
        omega))[k.val]? with
    | none => Sum.inl ()
    | some cell => Sum.inr
        (cell.enabled, (cell.recordedArm, (cell.reward, cell.rate)))

/-- Proof-erasure does not lose information about a finite list of queue
inputs when the list length is bounded by the readout width. -/
theorem numericalListReadout_injective {n : ℕ}
    (u v : List (RecordedQueueRun.RoundInput p.K))
    (hu : u.length ≤ n) (hv : v.length ≤ n)
    (hread : (fun k : Fin n =>
      match u[k.val]? with
      | none => (Sum.inl () : Unit ⊕ NumericalCellReadout p)
      | some cell => Sum.inr
          (cell.enabled, (cell.recordedArm, (cell.reward, cell.rate)))) =
      fun k : Fin n =>
        match v[k.val]? with
        | none => (Sum.inl () : Unit ⊕ NumericalCellReadout p)
        | some cell => Sum.inr
            (cell.enabled, (cell.recordedArm, (cell.reward, cell.rate)))) :
    u = v := by
  have hlen : u.length = v.length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hi : u.length < n := lt_of_lt_of_le hlt hv
      let i : Fin n := ⟨u.length, hi⟩
      have h := congrFun hread i
      have hu : u[u.length]? = none := List.getElem?_eq_none (Nat.le_refl _)
      have hv' : v[u.length]? = some (v[u.length]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      simp only [i, hu, hv'] at h
      cases h
    · have hi : v.length < n := lt_of_lt_of_le hlt hu
      let i : Fin n := ⟨v.length, hi⟩
      have h := congrFun hread i
      have hv' : v[v.length]? = none := List.getElem?_eq_none (Nat.le_refl _)
      have hu' : u[v.length]? = some (u[v.length]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      simp only [i, hu', hv'] at h
      cases h
  apply List.ext_getElem hlen
  intro i hiU hiV
  have h := congrFun hread ⟨i, by omega⟩
  simp only [List.getElem?_eq_getElem hiU, List.getElem?_eq_getElem hiV] at h
  injection h with hfields
  cases hU : u[i] with
  | mk uenabled uarm ureward urate huneg hule huRate =>
    cases hV : v[i] with
    | mk venabled varm vreward vrate hvneg hvle hvRate =>
      simp only [hU, hV] at hfields
      rcases Prod.mk.inj hfields with ⟨henabled, hfields⟩
      rcases Prod.mk.inj hfields with ⟨harm, hfields⟩
      rcases Prod.mk.inj hfields with ⟨hreward, hrate⟩
      cases henabled
      cases harm
      cases hreward
      cases hrate
      have hproof1 : huneg = hvneg := Subsingleton.elim _ _
      have hproof2 : hule = hvle := Subsingleton.elim _ _
      have hproof3 : huRate = hvRate := Subsingleton.elim _ _
      cases hproof1
      cases hproof2
      cases hproof3
      rfl

private def sourceActiveRunInput
    (z : SourceZ rate rewards C_star C_h q t s hs) : ActiveRunInput rate s :=
  ⟨(ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h
      (sourceCrossing rate rewards C_star C_h q t s hs z),
    (z.val.1.2, (q, rewards))),
    by
      have hmode := (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z.val rewards C_star C_h
        (sourceCrossing rate rewards C_star C_h q t s hs z)).activeAtStart
      rw [sourceElapsed rate rewards C_star C_h q t s hs z] at hmode
      exact hmode⟩

private theorem measurable_of_some {X : Type*} {α : Type*} [MeasurableSpace X]
    [MeasurableSpace α] (f : X → α) (hf : Measurable (fun x => some (f x))) :
    Measurable f := by
  let e : Option α ≃ α ⊕ PUnit := Equiv.optionEquivSumPUnit α
  have hs : Measurable (fun x => e (some (f x))) := measurable_comap_iff.mp hf
  intro u hu
  convert hs hu.inl_image using 1
  ext x
  change f x ∈ u ↔ (Sum.inl (f x) : α ⊕ PUnit) ∈ Sum.inl '' u
  simp only [Set.mem_image, Sum.inl.injEq, exists_eq_right]

private theorem sourceSelectedIndex
    (z : SourceZ rate rewards C_star C_h q t s hs) :
    ActualInitializationPhysicalStep.selectedRowIndex p z.val = q := by
  exact (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
    p z.val).symm.trans z.property.1

private theorem measurable_sourceLaunchState :
    Measurable (fun z : SourceZ rate rewards C_star C_h q t s hs =>
      ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h
        (sourceCrossing rate rewards C_star C_h q t s hs z)) := by
  apply measurable_comap_iff.mpr
  apply measurable_of_some
  have hsource : Measurable (fun z : SourceZ rate rewards C_star C_h q t s hs => z.val) :=
    measurable_subtype_coe
  have h := (ReferenceCorrectedLaunchMeasurability.measurable_correctedLaunch_encodeState
    rate rewards C_star C_h).comp hsource
  convert h using 1
  funext z
  change some (ReferenceActivePhysicalStepMeasurability.encodeState
      (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h
        (sourceCrossing rate rewards C_star C_h q t s hs z))) =
    Option.map ReferenceActivePhysicalStepMeasurability.encodeState
      (ReferenceCorrectedInitializationLaunch.correctedLaunch rate z.val rewards C_star C_h)
  rw [ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState]
  rfl

private theorem measurable_sourceActiveRunInput :
    Measurable (sourceActiveRunInput rate rewards C_star C_h q t s hs) := by
  have hdata : Measurable (fun z : SourceZ rate rewards C_star C_h q t s hs =>
      (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h
          (sourceCrossing rate rewards C_star C_h q t s hs z),
        (z.val.1.2, (q, rewards)))) := by
    exact measurable_sourceLaunchState rate rewards C_star C_h q t s hs |>.prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_subtype_coe)).prodMk
        (measurable_const.prodMk measurable_const))
  exact hdata.subtype_mk

private theorem sourceActiveRun_eq_actual
    (z : SourceZ rate rewards C_star C_h q t s hs) :
    ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s)
      (by omega) (sourceActiveRunInput rate rewards C_star C_h q t s hs z) =
    ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z.val rewards C_star C_h
      (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
      (sourceCountSpan rate rewards C_star C_h q t s hs z) := by
  have hrow := sourceSelectedIndex rate rewards C_star C_h q t s hs z
  unfold ReferenceActiveHorizonMeasurability.runOfInput sourceActiveRunInput
    ReferenceFirstWindowNumericalStream.actualFirstLiveRun
  simp only [sourceElapsed]
  rw [hrow]

private def runPrefixInput (start k : ℕ) (hspan : start + (k + 1) ≤ p.T)
    (input : ActiveRunInput rate start) :
    ReferenceActivePhysicalStep.RoundInput p rate :=
  ReferenceActivePhysicalHorizon.roundInputAt input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 start input.property
    (ReferenceActiveHorizonMeasurability.runOfInput start k (by omega) input)
    ⟨start + k, by omega, by omega⟩

private theorem measurable_runPrefixInput (start k : ℕ)
    (hspan : start + (k + 1) ≤ p.T) :
    Measurable (runPrefixInput (rate := rate) (t := t) (s := s) start k hspan) := by
  have hdata : Measurable (fun input : ActiveRunInput rate start => input.val) :=
    measurable_subtype_coe
  have hcoordinates : Measurable (fun input : ActiveRunInput rate start =>
      ((ReferenceActiveHorizonMeasurability.runOfInput start k (by omega) input).finalState,
        (input.val.2.1,
          (input.val.2.2.1, ((⟨start + k, by omega⟩ : Fin p.T), input.val.2.2.2))))) :=
    (ReferenceActiveHorizonMeasurability.measurable_runFinalState start k (by omega)).prodMk
      ((measurable_fst.comp (measurable_snd.comp hdata)).prodMk
        ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hdata))).prodMk
          (measurable_const.prodMk
            (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hdata))))))
  apply measurable_comap_iff.mpr
  exact hcoordinates.subtype_mk (h := fun input =>
    (runPrefixInput (rate := rate) (t := t) (s := s) start k hspan input).active)

private theorem runRecords_eq_ofFn (start count : ℕ) (hspan : start + count ≤ p.T)
    (input : ActiveRunInput rate start) :
    (ReferenceActiveHorizonMeasurability.runOfInput start count hspan input).records =
      List.ofFn (fun k : Fin count =>
        (⟨runPrefixInput (rate := rate) (t := t) (s := s) start k.val (by omega) input,
          ReferenceActivePhysicalStep.step
            (runPrefixInput (rate := rate) (t := t) (s := s) start k.val (by omega) input), rfl⟩ :
          ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) := by
  induction count with
  | zero =>
      exact ReferenceActivePhysicalHorizon.run_zero_records _ _ _ _ _ _ _
  | succ count ih =>
      rw [ReferenceActiveHorizonMeasurability.runOfInput,
        ReferenceActivePhysicalHorizon.run_successor_step]
      rw [(ReferenceActivePhysicalHorizon.foldRound_equations _ _ _ _ _ _ _ _).2]
      rw [List.ofFn_succ', List.concat_eq_append]
      change (ReferenceActiveHorizonMeasurability.runOfInput start count (by omega) input).records ++
          [_] = _
      rw [ih (by omega)]
      rfl

private theorem sourceRunRecords_eq_ofFn
    (z : SourceZ rate rewards C_star C_h q t s hs) :
    (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z.val rewards C_star C_h
      (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
      (sourceCountSpan rate rewards C_star C_h q t s hs z)).records =
      List.ofFn (fun k : Fin (t.val - s) =>
        (⟨runPrefixInput (rate := rate) (t := t) (s := s) s k.val (by omega)
            (sourceActiveRunInput rate rewards C_star C_h q t s hs z),
          ReferenceActivePhysicalStep.step
            (runPrefixInput (rate := rate) (t := t) (s := s) s k.val (by omega)
              (sourceActiveRunInput rate rewards C_star C_h q t s hs z)), rfl⟩ :
          ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) := by
  rw [← sourceActiveRun_eq_actual rate rewards C_star C_h q t s hs z]
  exact runRecords_eq_ofFn (rate := rate) (t := t) (s := s) s (t.val - s) (by omega)
    (sourceActiveRunInput rate rewards C_star C_h q t s hs z)

/-- The actual count-`n` numerical list never has more than `n` entries. -/
theorem numericalCountPast_length_le
    (control0 : TimeControl p)
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)) :
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
      z.property.2.1 (t.val - s)
      (by
        have he : ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s :=
          by simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.property.2.2
        rw [he]
        omega)).length ≤ t.val - s := by
  let _control0 := control0
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val rewards
    C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
    (sourceCountSpan rate rewards C_star C_h q t s hs z)
  let run := ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z.val rewards
    C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
    (sourceCountSpan rate rewards C_star C_h q t s hs z)
  have hprefix : window.IsPrefix run.records := by
    dsimp [window, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow, run]
    exact List.takeWhile_prefix _
  have hrun : run.records.length = t.val - s := by
    dsimp [run, ReferenceFirstWindowNumericalStream.actualFirstLiveRun]
    exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length rate z.val rewards
    C_star C_h z.property.2.1 (t.val - s) (by
      have he : ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s :=
        by simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.property.2.2
      rw [he]
      omega)]
  exact hprefix.length_le.trans_eq hrun

private theorem measurable_sigma_sections {ι : Type*} {F : ι → Type*}
    [∀ i, MeasurableSpace (F i)] {Y : Type*} [MeasurableSpace Y]
    (f : Sigma F → Y) (hf : ∀ i, Measurable (fun x : F i => f ⟨i, x⟩)) :
    Measurable f := by
  intro u hu
  change MeasurableSet[(⨅ i, (inferInstance : MeasurableSpace (F i)).map (Sigma.mk i))]
    {x | f x ∈ u}
  rw [MeasurableSpace.measurableSet_iInf]
  intro i
  rw [MeasurableSpace.map_def]
  exact hf i hu

private def preparedStatusTag {rate : ReferenceActivePhysicalStep.RateInput p}
    (z : FollowerVaryingActivationMeasurability.VaryingPreparedOutput p rate) : Option (Fin 3) :=
  z.2.2.2.map fun data => FollowerDownMeasurability.followerStatusCode
    (FollowerDownMeasurability.followerStatusOfCode data.1.1.1.status)

private theorem measurable_preparedStatusTag {rate : ReferenceActivePhysicalStep.RateInput p} :
    Measurable (preparedStatusTag (p := p) (rate := rate)) := by
  have hs : Measurable (fun z : FollowerObservationStageMeasurabilityRepair.CarriedState p rate =>
      FollowerDownMeasurability.followerStatusCode
        (FollowerDownMeasurability.followerStatusOfCode z.1.1.status)) := by
    apply measurable_sigma_sections
    intro index
    change Measurable (fun _ => FollowerDownMeasurability.followerStatusCode
      (FollowerDownMeasurability.followerStatusOfCode index.1.status))
    exact measurable_const
  have ht : Measurable (fun z : Unit ⊕
      (FollowerPrepareJointMeasurability.CarriedState p rate ×
        FollowerPrepareJointMeasurability.LocalMemoryCode p) =>
      z.elim (fun _ => (none : Option (Fin 3)))
        (fun data => some (FollowerDownMeasurability.followerStatusCode
          (FollowerDownMeasurability.followerStatusOfCode data.1.1.1.status)))) :=
    Measurable.sumElim measurable_const
      ((measurable_of_countable (some : Fin 3 → Option (Fin 3))).comp (hs.comp measurable_fst))
  apply measurable_sigma_sections
  intro activation
  convert ht.comp ((FollowerPrepareJointMeasurability.measurable_incomingConfigurationToSum rate).comp
    (measurable_snd.comp measurable_snd)) using 1
  funext z
  cases hi : z.2.2 <;>
    simp only [preparedStatusTag, Function.comp_def,
      FollowerPrepareJointMeasurability.incomingConfigurationToSum, hi,
      Option.map_none, Option.map_some, Sum.elim_inl, Sum.elim_inr]

private theorem preparedStatusTag_actual
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (i : Fin (p.m - 1)) :
    preparedStatusTag (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode record.input i) =
      some (FollowerDownMeasurability.followerStatusCode (cell.states i).status) := by
  let tag (config : DeclaredFollowerLocalRound.LocalConfiguration p rate) : Option (Fin 3) :=
    match config with
    | .dagger => none
    | .ordinary state _ => some (FollowerDownMeasurability.followerStatusCode state.status)
  have h := congrArg (fun prepared => tag prepared.configuration)
    (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode_reconstruct record.input i)
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have ho := cell.ordinary i
  rw [hprep] at ho
  rw [ho] at h
  change _ = some (FollowerDownMeasurability.followerStatusCode (cell.states i).status) at h
  convert h using 1
  generalize hz : ReferenceActivePhysicalStepMeasurability.preparedFollowerCode record.input i = z
  cases hi : z.2.2.2 <;>
    simp only [preparedStatusTag, FollowerPrepareJointMeasurability.preparedRoundOfOutput,
      FollowerPrepareJointMeasurability.localConfigurationOfIncoming, hi,
      Option.map_none, Option.map_some, tag,
      FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
      FollowerDownMeasurability.followerStateOfCode]

private def scoreVector (p : Parameters) (scores : Fin p.K → ℕ) : Fin p.K → ℝ :=
  fun a => ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p) (scores a)

private theorem sourceWeights_register_range
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (hunit : ∀ a, r.payload.anchor a = 1) :
    ∃ scores : Fin p.K → ℕ,
      ReferenceFirstWindowNumericalStream.sourceWeights r.payload r.complementWeights =
        scoreVector p scores := by
  classical
  refine ⟨fun a => if ha : a ∈ r.payload.slowSet.val then 0 else
    r.complementScores ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩, ?_⟩
  funext a
  by_cases ha : a ∈ r.payload.slowSet.val
  · simp only [ReferenceFirstWindowNumericalStream.sourceWeights, ha, dite_true,
      scoreVector, ScoreWeights.scoreWeight, pow_zero, hunit]
  · simp only [ReferenceFirstWindowNumericalStream.sourceWeights, ha, dite_false,
      scoreVector, CoordinatorLiveChoiceRecorderStep.Registers.complementWeights]

private theorem recordingMap_congr
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (a b : SnapshotRecordingKernel.Regime p) (va vb wa wb : Fin p.K → ℝ)
    (hva : ∀ j, 0 < va j) (hvb : ∀ j, 0 < vb j)
    (hwa : ∀ j, 0 < wa j) (hwb : ∀ j, 0 < wb j)
    (hloA : ∀ j, va j ≤ wa j) (hloB : ∀ j, vb j ≤ wb j)
    (hhiA : ∀ j, wa j ≤ 2 * va j) (hhiB : ∀ j, wb j ≤ 2 * vb j)
    (hab : a = b) (hv : va = vb) (hw : wa = wb)
    (row : CanonicalRecordingSlice.Slice p.m p.K) :
    SnapshotRecordingKernel.recordingMap p a true rate.eta.val rate.eta.property rate.sourceCap
      va wa hva hwa hloA hhiA row =
    SnapshotRecordingKernel.recordingMap p b true rate.eta.val rate.eta.property rate.sourceCap
      vb wb hvb hwb hloB hhiB row := by
  cases hab
  cases hv
  cases hw
  rfl

private theorem measurable_cell_readout
    {rate : ReferenceActivePhysicalStep.RateInput p} {X : Type*} [MeasurableSpace X]
    (r : X → ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : ∀ x, ReferenceFirstWindowNumericalStream.ActualLiveSourceCell (r x))
    (hr : Measurable (fun x => (r x).input))
    (hunit : ∀ x a, (c x).selected.view.payload.anchor a = 1)
    (hscore : ∀ x, ∃ scores : Fin p.K → ℕ,
      ReferenceFirstWindowNumericalStream.sourceWeights (c x).selected.view.payload
        (c x).selected.view.complementWeights = scoreVector p scores) :
    Measurable (fun x => ((c x).input.enabled,
      ((c x).input.recordedArm, ((c x).input.reward, (c x).input.rate)))) := by
  classical
  have hsel : Measurable (fun x =>
      ReferenceLiveDispatchOutputMeasurability.encodeSelection (c x).selected) := by
    apply measurable_of_some
    have h := measurable_fst.comp
      (ReferenceActiveStepCompositionMeasurability.measurable_physicalCode.comp hr)
    convert h using 1
    funext x
    have hp : (r x).output.preparation.coordinator = ReferenceActivePhysicalStep.dispatch (r x).input := by
      rw [(r x).output_eq]
      rfl
    change some _ = ((ReferenceActivePhysicalStep.dispatch (r x).input).selection.map _)
    rw [← hp, (c x).selection_actual]
    rfl
  have hview := (comap_measurable
    (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate))).comp
      (measurable_fst.comp hsel)
  have hpayload := measurable_fst.comp hview
  have hpobs := (comap_measurable
    (LaterAssignmentStartMeasurability.payloadObservation (p := p) (eta := rate.eta))).comp hpayload
  have hslow := (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hpobs)))
  have haux := (AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary).comp hpayload
  have hpending := measurable_fst.comp (measurable_snd.comp hview)
  have hstatus : Measurable (fun x => fun i : Fin (p.m - 1) =>
      FollowerDownMeasurability.followerStatusCode ((c x).states i).status) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_to_countable'
    intro v
    have ht := (measurable_preparedStatusTag.comp
      (ReferenceActivePhysicalStepMeasurability.measurable_preparedFollowerCode i)).comp hr
    convert (measurableSet_singleton (some v)).preimage ht using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_def]
    rw [preparedStatusTag_actual (r x) (c x) i]
    simp only [Option.some.injEq]
  let weights (x : X) := ReferenceFirstWindowNumericalStream.sourceWeights
    (c x).selected.view.payload (c x).selected.view.complementWeights
  have hw : Measurable weights := by
    apply measurable_pi_iff.mpr
    intro a
    have hfast := (measurable_pi_apply a).comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hview)))
    have hm : MeasurableSet {x | a ∈ (c x).selected.view.payload.slowSet.val} :=
      (Set.toFinite {u : Finset (Fin p.K) | a ∈ u}).measurableSet.preimage hslow
    have h : Measurable (fun x => if a ∈ (c x).selected.view.payload.slowSet.val then
        (1 : ℝ) else ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector
          (c x).selected.view a) := measurable_const.ite hm hfast
    convert h using 1
    funext x
    by_cases ha : a ∈ (c x).selected.view.payload.slowSet.val
    · simp only [weights, ReferenceFirstWindowNumericalStream.sourceWeights, ha,
        dite_true, ite_true, hunit]
    · have hf : a ∈ CanonicalFastSampling.fastArmFinset (c x).selected.view.payload.slowSet :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩
      simp only [weights, ReferenceFirstWindowNumericalStream.sourceWeights, ha,
        dite_false, ite_false, ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector,
        hf, dite_true]
  let WeightImage := Set.range (scoreVector p)
  let : Countable WeightImage := (Set.countable_range (scoreVector p)).to_subtype
  let key (x : X) := ((c x).selected.view.payload.slowSet.val,
    ((c x).selected.view.payload.auxiliaryArm, ((c x).selected.view.pendingAtChoice,
      ((fun i => FollowerDownMeasurability.followerStatusCode ((c x).states i).status),
        (⟨weights x, by obtain ⟨scores, h⟩ := hscore x; exact ⟨scores, h.symm⟩⟩ : WeightImage)))))
  have hkey : Measurable key := hslow.prodMk (haux.prodMk (hpending.prodMk
    (hstatus.prodMk hw.subtype_mk)))
  let KeyRange := Set.range key
  let code (x : X) : KeyRange := ⟨key x, x, rfl⟩
  let representative (k : KeyRange) : X := Classical.choose k.property
  let sourceMap (k : KeyRange) :=
    let z := representative k
    let selected := (c z).selected
    SnapshotRecordingKernel.recordingMap p
      (.live selected.view.payload.assignment
        { missing := selected.view.pendingAtChoice, status := fun i => ((c z).states i).status })
      true rate.eta.val rate.eta.property rate.sourceCap selected.view.payload.anchor (weights z)
      selected.view.payload.anchor_pos
      (ReferenceFirstWindowNumericalStream.sourceWeights_pos selected.view.payload
        selected.view.complementWeights selected.view.cutoff (r z).input.time (c z).choiceInputsValid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_lower selected.view.payload
        selected.view.complementWeights selected.view.cutoff (r z).input.time (c z).choiceInputsValid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_upper selected.view.payload
        selected.view.complementWeights selected.view.cutoff (r z).input.time (c z).choiceInputsValid)
  have hslice : Measurable (fun x => ((r x).input.row.2 (r x).input.time).1) := by
    have heval : Measurable (fun z : CompletePublicTable.CompleteRow p × Fin p.T =>
        (z.1.2 z.2).1) := by
      apply measurable_from_prod_countable_left
      intro t
      exact (ContinuousLearningRows.measurable_sliceAt t).comp measurable_snd
    exact heval.comp ((ReferenceActivePhysicalStepMeasurability.measurable_row.comp hr).prodMk
      (ReferenceActivePhysicalStepMeasurability.measurable_time.comp hr))
  have hm (k : KeyRange) : Measurable (fun x => sourceMap k (((r x).input.row.2 (r x).input.time).1)) :=
    (SnapshotRecordingKernel.measurable_recordingMap p _ _ _ _ _ _ _ _ _ _ true).comp hslice
  have h := CoordinatorCollectionRunMeasurabilityRepair.measurable_of_countable_cases
    code hkey.subtype_mk (fun k x => sourceMap k (((r x).input.row.2 (r x).input.time).1)) hm
  have hmarker : Measurable (fun x => (c x).input.recordedArm) := by
    convert h using 1
    funext x
    have hk : key (representative (code x)) = key x := Classical.choose_spec (code x).property
    have hslowEq := congrArg (fun k => k.1) hk
    have hauxEq := congrArg (fun k => k.2.1) hk
    have hpendingEq := congrArg (fun k => k.2.2.1) hk
    have hstatusEq := congrArg (fun k => k.2.2.2.1) hk
    have hwEq := congrArg (fun k => k.2.2.2.2) hk
    dsimp only [key] at hslowEq hauxEq hpendingEq hstatusEq hwEq
    have hs : (c (representative (code x))).selected.view.payload.slowSet =
        (c x).selected.view.payload.slowSet := Subtype.ext hslowEq
    have ha : (c (representative (code x))).selected.view.payload.anchor =
        (c x).selected.view.payload.anchor := funext fun a => (hunit _ a).trans (hunit _ a).symm
    have hassignment : (c (representative (code x))).selected.view.payload.assignment =
        (c x).selected.view.payload.assignment := by
      simp only [AssignmentStartPayload.Input.assignment, hs, hauxEq]
    have hstates := congrArg (fun values => fun i =>
      FollowerDownMeasurability.followerStatusOfCode (values i)) hstatusEq
    simp only [FollowerDownMeasurability.followerStatusOfCode_code] at hstates
    have hweights := congrArg Subtype.val hwEq
    dsimp only [weights] at hweights
    have regimeCongr (a b : ActiveRoundActions.Assignment p.m p.K)
        (pa pb : Finset (Fin (p.m - 1)))
        (sa sb : Fin (p.m - 1) → ActiveRoundActions.FollowerStatus)
        (hab : a = b) (hp : pa = pb) (hs : sa = sb) :
        SnapshotRecordingKernel.Regime.live (p := p) a ⟨pa, sa⟩ = .live b ⟨pb, sb⟩ := by
      cases hab
      cases hp
      cases hs
      rfl
    have hregime := regimeCongr _ _ _ _ _ _ hassignment hpendingEq hstates
    rw [(c x).recordedArm_eq]
    dsimp only [ReferenceFirstWindowNumericalStream.sourceArm, sourceMap, weights]
    exact recordingMap_congr (rate := rate) _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hregime.symm ha.symm hweights.symm _
  have hrate := AssignmentPayloadDerivedMeasurability.measurable_inputRate.comp hpayload
  have hreward : Measurable (fun x => fun a : Fin p.K =>
      (((r x).input.rewards (r x).input.time a).val : ℝ) / (D p : ℝ)) :=
    (measurable_of_countable (fun z : ActualInitializationPhysicalStep.GridRewardTable p × Fin p.T =>
      fun a : Fin p.K => ((z.1 z.2 a).val : ℝ) / (D p : ℝ))).comp
      ((ReferenceActivePhysicalStepMeasurability.measurable_rewards.comp hr).prodMk
        (ReferenceActivePhysicalStepMeasurability.measurable_time.comp hr))
  have henabled : Measurable (fun _ : X => true) := measurable_const
  have hall := henabled.prodMk (hmarker.prodMk (hreward.prodMk hrate))
  convert hall using 1
  funext x
  rw [(c x).input_eq]
  rfl

local instance (priority := 5000) codeCoordinatorFailureOptionMeasurableSpace :
    MeasurableSpace (Option ReferenceActivePhysicalStep.CoordinatorFailure) :=
  @LaterAssignmentStartMeasurability.optionMeasurableSpace _ inferInstance

private theorem laterOptionSpace_eq_top_local {α : Type*} (mα : MeasurableSpace α)
    (hα : mα = ⊤) :
    @LaterAssignmentStartMeasurability.optionMeasurableSpace α mα = ⊤ := by
  subst mα
  let _ : MeasurableSpace α := ⊤
  let e := Equiv.optionEquivSumPUnit α
  have hsum : (inferInstance : MeasurableSpace (α ⊕ PUnit)) = ⊤ := by
    ext s
    rw [measurableSet_sum_iff]
    simp
  have hcomap : (MeasurableSpace.comap e (⊤ : MeasurableSpace (α ⊕ PUnit))) = ⊤ := by
    apply MeasurableSpace.ext
    intro s
    rw [MeasurableSpace.measurableSet_comap]
    constructor
    · intro _
      trivial
    · intro _
      refine ⟨e '' s, trivial, ?_⟩
      ext x
      simp [e.injective]
  unfold LaterAssignmentStartMeasurability.optionMeasurableSpace
  rw [hsum]
  exact hcomap

private abbrev CoordinatorCode (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate

private abbrev CollectionTailCode (p : Parameters) (rate : RateInput p) :=
  ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate

private def incomingLiveCoordinatorCode {rate : RateInput p}
    (code : CoordinatorCode p rate) : Bool :=
  match code with
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr _) => false

private theorem measurable_incomingLiveCoordinatorCode {rate : RateInput p} :
    Measurable (incomingLiveCoordinatorCode (p := p) (rate := rate)) := by
  apply Measurable.sumElim
  · exact measurable_const
  · apply Measurable.sumElim
    · exact measurable_const
    · exact measurable_const

private def collectionCoordinatorCode {rate : RateInput p}
    (code : CoordinatorCode p rate) : Bool :=
  match code with
  | .inl _ => false
  | .inr (.inl _) => false
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr _)) => false

private theorem measurable_collectionCoordinatorCode {rate : RateInput p} :
    Measurable (collectionCoordinatorCode (p := p) (rate := rate)) := by
  apply Measurable.sumElim
  · exact measurable_const
  · apply Measurable.sumElim
    · exact measurable_const
    · apply Measurable.sumElim
      · exact measurable_const
      · exact measurable_const

private def collectionFailureCode
    (failure : Option ReferenceActivePhysicalStep.CoordinatorFailure) : Bool :=
  match failure with
  | some (.collection _) => true
  | _ => false

private theorem measurable_collectionFailureCode :
    Measurable collectionFailureCode := by
  have hopt : codeCoordinatorFailureOptionMeasurableSpace = ⊤ := by
    unfold codeCoordinatorFailureOptionMeasurableSpace
    exact laterOptionSpace_eq_top_local ⊤ rfl
  change @Measurable (Option ReferenceActivePhysicalStep.CoordinatorFailure) Bool
    codeCoordinatorFailureOptionMeasurableSpace inferInstance collectionFailureCode
  rw [hopt]
  intro s hs
  trivial

/-- A cutoff tag is read from the actual returned collection state or
collection-stage failure. The incoming state tag is checked separately. -/
private def collectionTailTag {rate : RateInput p}
    (code : CollectionTailCode p rate) : Bool :=
  collectionCoordinatorCode code.1 || collectionFailureCode code.2.2.1

private theorem measurable_collectionTailTag (p : Parameters) (rate : RateInput p) :
    Measurable (collectionTailTag (p := p) (rate := rate)) := by
  have hleft : Measurable (fun code : CollectionTailCode p rate =>
      collectionCoordinatorCode code.1) :=
    measurable_collectionCoordinatorCode.comp measurable_fst
  have hright : Measurable (fun code : CollectionTailCode p rate =>
      collectionFailureCode code.2.2.1) :=
    measurable_collectionFailureCode.comp
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id)))
  have hpair : Measurable (fun code : CollectionTailCode p rate =>
      (collectionCoordinatorCode code.1, collectionFailureCode code.2.2.1)) :=
    hleft.prodMk hright
  exact (measurable_of_countable (fun bits : Bool × Bool => bits.1 || bits.2)).comp hpair

private def recordIncomingCoordinatorCode {rate : RateInput p}
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) : CoordinatorCode p rate :=
  code.2.1.1

private def recordPhysicalCode {rate : RateInput p}
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) :=
  code.2.2.1

private def recordCollectionTailCode {rate : RateInput p}
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) : CollectionTailCode p rate :=
  (recordPhysicalCode code).2.2.2.2

/-- The cutoff bit stored in an actual chronological record code. -/
private def cutoffRecordCode {rate : RateInput p}
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) : Bool :=
  incomingLiveCoordinatorCode (recordIncomingCoordinatorCode code) &&
    collectionTailTag (recordCollectionTailCode code)

private theorem measurable_cutoffRecordCode {rate : RateInput p} :
    Measurable (cutoffRecordCode (p := p) (rate := rate)) := by
  have hlive : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) =>
      incomingLiveCoordinatorCode (recordIncomingCoordinatorCode code)) := by
    exact measurable_incomingLiveCoordinatorCode.comp
      (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_id)))
  have htail : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) =>
      collectionTailTag (recordCollectionTailCode code)) := by
    have hphysical : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
        (p := p) (rate := rate) =>
        code.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
    have hrecordTailCode : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
        (p := p) (rate := rate) =>
        recordCollectionTailCode code) := by
      exact measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp hphysical)))
    exact (measurable_collectionTailTag p rate).comp hrecordTailCode
  exact (measurable_of_countable (fun bits : Bool × Bool => bits.1 && bits.2)).comp
    (hlive.prodMk htail)

private def collectionObservationTag {rate : RateInput p}
    (observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate) : Bool :=
  match observation.failure with
  | some (.collection _) => true
  | _ =>
      match observation.configuration with
      | .collection _ _ _ => true
      | _ => false

private theorem collectionTailTag_encodeObservation {rate : RateInput p}
    (observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate) :
    collectionTailTag (p := p) (rate := rate)
        (ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation observation) =
      collectionObservationTag observation := by
  cases observation with
  | mk configuration bank failure recording up =>
      cases failure with
      | none =>
          cases configuration <;>
            simp [collectionTailTag, collectionCoordinatorCode, collectionFailureCode,
              collectionObservationTag,
              ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
      | some failure =>
          cases failure <;> cases configuration <;>
            simp [collectionTailTag, collectionCoordinatorCode, collectionFailureCode,
              collectionObservationTag,
              ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator]

private theorem collectionFinish_collectionObservationTag {rate : RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    collectionObservationTag
      (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut) = true := by
  unfold ReferenceActivePhysicalStep.collectionFinish
  cases hresult : cut.result with
  | invalid => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure]
  | success result =>
      cases hfinish : CoordinatorCollectionLedger.finishRound result.1 with
      | invalid => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hfinish]
      | rejected rejected => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hfinish]
      | success ledger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
              ledger.pending x.row with
          | error error => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
              hfinish, hclock]
          | ok clock => simp [collectionObservationTag, hfinish, hclock]
  | rejected result =>
      cases hfinish : CoordinatorCollectionLedger.finishRound result.1 with
      | invalid => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hfinish]
      | rejected rejected => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hfinish]
      | success ledger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
              ledger.pending x.row with
          | error error => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
              hfinish, hclock]
          | ok clock => simp [collectionObservationTag, hfinish, hclock]

private theorem collectionPostChoice_collectionObservationTag {rate : RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    collectionObservationTag
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights) = true := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hstart]
      | rejected rejected => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hstart]
      | success ledgerStarted =>
          simp only [hstart]
          exact collectionFinish_collectionObservationTag x payload started recording
            (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)

private theorem livePostChoice_collectionObservationTag {rate : RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    collectionObservationTag
      (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started) = false := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared registers started) with
  | none => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
      | error error => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hservice]
      | ok serviced =>
          cases hconfirm : CoordinatorLocalArmChoice.confirmationUpdate registers.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
              hservice]
          | some pending =>
              cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
                  pending x.row with
              | error error => simp [collectionObservationTag,
                  ReferenceActivePhysicalStep.coordinatorFailure, hservice,
                  hclock]
              | ok finished => simp [collectionObservationTag, hservice, hclock]

private theorem liveOutcome_collectionObservationTag {rate : RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x registers owned base))
    (hprepared : prepared.coordinator = .live registers owned base outcome) :
    collectionObservationTag prepared.observeCoordinator =
      match outcome with
      | .cutoffChosen _ _ _ _ _ _ _ _ _ _ => true
      | _ => false := by
  rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation prepared registers owned base
    outcome hprepared]
  cases outcome with
  | clockFailure failure proof =>
      simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
        ReferenceActivePhysicalStep.DispatchCut.selection]
  | initializerFailure dispatched start checked checkedEq =>
      simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
        ReferenceActivePhysicalStep.DispatchCut.selection]
  | localFailure dispatched start reason =>
      simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
        ReferenceActivePhysicalStep.DispatchCut.selection]
  | cutoffChosen dispatched start ledger initEq ledgerEq domain clock pending noAssign selected =>
      have hselection :
          (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
            (.cutoffChosen dispatched start ledger initEq ledgerEq domain clock pending noAssign selected)).selection ≠ none := by
        simp [ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt]
      have hpost := collectionPostChoice_collectionObservationTag x prepared
        registers.payload (ReferenceActivePhysicalStep.sharedLedger ledger)
        dispatched.startResult
        (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
      simpa [hselection] using hpost
  | continuingChosen dispatched start continuation selected =>
      have hselection :
          (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
            (.continuingChosen dispatched start continuation selected)).selection ≠ none := by
        simp [ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt]
      have hpost := livePostChoice_collectionObservationTag x prepared
        (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
        (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time)
        base dispatched.startResult
      simpa [hselection] using hpost

private theorem cutoffRecordCode_roundRecordCode {rate : RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    cutoffRecordCode (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      ReferenceCollectionPhaseHistory.cutoffChosen record.input := by
  have htail : collectionTailTag
      (recordCollectionTailCode (ReferenceActiveHorizonMeasurability.roundRecordCode record)) =
      collectionObservationTag
        (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator := by
    rw [show recordCollectionTailCode
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator by rfl]
    exact collectionTailTag_encodeObservation _
  change (incomingLiveCoordinatorCode
      (recordIncomingCoordinatorCode
        (ReferenceActiveHorizonMeasurability.roundRecordCode record)) &&
      collectionTailTag
        (recordCollectionTailCode
          (ReferenceActiveHorizonMeasurability.roundRecordCode record))) =
    ReferenceCollectionPhaseHistory.cutoffChosen record.input
  cases hstate : record.input.state.coordinator with
  | first =>
      have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
          .first (CoordinatorRoundDispatch.dispatchFirst
            (ReferenceActivePhysicalStep.firstInput record.input)) := by
        rw [ReferenceActivePhysicalStep.dispatch, hstate,
          CoordinatorRoundDispatch.dispatch]
        rfl
      have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
        simp [ReferenceCollectionPhaseHistory.cutoffChosen,
          ReferenceActivePhysicalStep.prepare, hdispatch]
      simp [recordIncomingCoordinatorCode,
        ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        incomingLiveCoordinatorCode, hstate, hcutoff]
  | live registers owned base =>
      have hdispatch := ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction
        record.input registers owned base hstate
      cases hout : CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput record.input registers owned base) with
      | clockFailure failure proof =>
          have hprepared' : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live registers owned base (.clockFailure failure proof) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have htag' := liveOutcome_collectionObservationTag record.input
            (ReferenceActivePhysicalStep.prepare record.input) registers owned base
            (.clockFailure failure proof) hprepared'
          have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
            simp [ReferenceCollectionPhaseHistory.cutoffChosen,
              ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          rw [htail, htag']
          simp [recordIncomingCoordinatorCode,
            ReferenceActiveHorizonMeasurability.roundRecordCode,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            incomingLiveCoordinatorCode, hstate, hcutoff]
      | initializerFailure dispatched start checked checkedEq =>
          have hprepared' : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live registers owned base (.initializerFailure dispatched start checked checkedEq) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have htag' := liveOutcome_collectionObservationTag record.input
            (ReferenceActivePhysicalStep.prepare record.input) registers owned base
            (.initializerFailure dispatched start checked checkedEq) hprepared'
          have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
            simp [ReferenceCollectionPhaseHistory.cutoffChosen,
              ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          rw [htail, htag']
          simp [recordIncomingCoordinatorCode,
            ReferenceActiveHorizonMeasurability.roundRecordCode,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            incomingLiveCoordinatorCode, hstate, hcutoff]
      | localFailure dispatched start reason =>
          have hprepared' : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live registers owned base (.localFailure dispatched start reason) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have htag' := liveOutcome_collectionObservationTag record.input
            (ReferenceActivePhysicalStep.prepare record.input) registers owned base
            (.localFailure dispatched start reason) hprepared'
          have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
            simp [ReferenceCollectionPhaseHistory.cutoffChosen,
              ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          rw [htail, htag']
          simp [recordIncomingCoordinatorCode,
            ReferenceActiveHorizonMeasurability.roundRecordCode,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            incomingLiveCoordinatorCode, hstate, hcutoff]
      | cutoffChosen dispatched start ledger initEq ledgerEq domain clock pending noAssign selected =>
          have hprepared' : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live registers owned base
                (.cutoffChosen dispatched start ledger initEq ledgerEq domain clock pending noAssign selected) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have htag' := liveOutcome_collectionObservationTag record.input
            (ReferenceActivePhysicalStep.prepare record.input) registers owned base
            (.cutoffChosen dispatched start ledger initEq ledgerEq domain clock pending noAssign selected)
            hprepared'
          have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = true := by
            simp [ReferenceCollectionPhaseHistory.cutoffChosen,
              ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          rw [htail, htag']
          simp [recordIncomingCoordinatorCode,
            ReferenceActiveHorizonMeasurability.roundRecordCode,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            incomingLiveCoordinatorCode, hstate, hcutoff]
      | continuingChosen dispatched start continuation selected =>
          have hprepared' : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live registers owned base (.continuingChosen dispatched start continuation selected) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have htag' := liveOutcome_collectionObservationTag record.input
            (ReferenceActivePhysicalStep.prepare record.input) registers owned base
            (.continuingChosen dispatched start continuation selected) hprepared'
          have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
            simp [ReferenceCollectionPhaseHistory.cutoffChosen,
              ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          rw [htail, htag']
          simp [recordIncomingCoordinatorCode,
            ReferenceActiveHorizonMeasurability.roundRecordCode,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            incomingLiveCoordinatorCode, hstate, hcutoff]
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
            .collection payload ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)) := by
          rw [ReferenceActivePhysicalStep.dispatch, hstate]
          simp only [dite_eq_left hvalid, CoordinatorRoundDispatch.dispatch]
          rfl
        have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
          simp [ReferenceCollectionPhaseHistory.cutoffChosen,
            ReferenceActivePhysicalStep.prepare, hdispatch]
        simp [recordIncomingCoordinatorCode,
          ReferenceActiveHorizonMeasurability.roundRecordCode,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          incomingLiveCoordinatorCode, hstate, hcutoff]
      · have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
            .invalidCollectionCutoff := by
          rw [ReferenceActivePhysicalStep.dispatch, hstate]
          simp [hvalid]
        have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
          simp [ReferenceCollectionPhaseHistory.cutoffChosen,
            ReferenceActivePhysicalStep.prepare, hdispatch]
        simp [recordIncomingCoordinatorCode,
          ReferenceActiveHorizonMeasurability.roundRecordCode,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          incomingLiveCoordinatorCode, hstate, hcutoff]
  | dagger =>
      have hdispatch : ReferenceActivePhysicalStep.dispatch record.input = .dagger := by
        rw [ReferenceActivePhysicalStep.dispatch, hstate]
      have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
        simp [ReferenceCollectionPhaseHistory.cutoffChosen,
          ReferenceActivePhysicalStep.prepare, hdispatch]
      simp [recordIncomingCoordinatorCode,
        ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        incomingLiveCoordinatorCode, hstate, hcutoff]

private theorem sourceCell_anchor_one
    (z : SourceZ rate rewards C_star C_h q t s hs)
    (k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val rewards
      C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
      (sourceCountSpan rate rewards C_star C_h q t s hs z)).length) :
    ∀ a : Fin p.K,
      (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
        (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
        (sourceCountSpan rate rewards C_star C_h q t s hs z) k).selected.view.payload.anchor a = 1 := by
  classical
  let hc := sourceCrossing rate rewards C_star C_h q t s hs z
  let span := sourceCountSpan rate rewards C_star C_h q t s hs z
  let I := ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z.val rewards C_star C_h hc
  let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z.val rewards C_star C_h hc
    (t.val - s) span
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val rewards C_star C_h hc
    (t.val - s) span
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
    hc (t.val - s) span k
  have hcount : 0 < t.val - s := by
    have hw : W.IsPrefix E.records := List.takeWhile_prefix _
    have hlen : E.records.length = t.val - s := by
      dsimp [E, ReferenceFirstWindowNumericalStream.actualFirstLiveRun]
      exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    exact (Nat.zero_lt_of_lt k.isLt).trans_le (hw.length_le.trans_eq hlen)
  have hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed < p.T := by
    rw [sourceElapsed rate rewards C_star C_h q t s hs z]
    exact lt_of_le_of_lt hs t.isLt
  have hbirth := ReferenceFirstDownRecoveryBudget.run_first_selected_payload I z.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ (t.val - s) span
    seed.activeAtStart seed.coordinatorFirst k cell.selected cell.selection_actual
  obtain ⟨birth, hmem, htime, hbirth, _⟩ := hbirth
  have hfirst : ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
      rate z.val rewards C_star C_h hc hs ∈ E.records := by
    obtain ⟨tail, htail⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
      I z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)
      rewards _ 1 ((t.val - s) - 1) (by omega) seed.activeAtStart
    have htail' : E.records =
        (ReferenceFirstLaunchNumericalCell.firstPhysicalRun rate z.val rewards C_star C_h hc hs).records ++ tail := by
      simpa only [E, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
        ReferenceFirstLaunchNumericalCell.firstPhysicalRun, I,
        Nat.add_sub_of_le hcount] using htail
    rw [htail', ReferenceFirstLaunchNumericalCell.firstPhysicalRun_records]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  have hfirstInputs := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord_source_inputs
    rate z.val rewards C_star C_h hc hs
  have heq : birth = ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
      rate z.val rewards C_star C_h hc hs :=
    ReferenceAssignmentPayloadChronology.run_records_time_injective I z.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ (t.val - s) span
      seed.activeAtStart hmem hfirst (htime.trans hfirstInputs.2.1.symm)
  rw [heq] at hbirth
  have hdispatch : (ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
      rate z.val rewards C_star C_h hc hs).output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch
        (ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h hc hs).input := by
    rw [(ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h hc hs).output_eq]
    rfl
  have hfirstState : (ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
      rate z.val rewards C_star C_h hc hs).input.state.coordinator = .first := by
    rw [hfirstInputs.1]
    exact seed.coordinatorFirst
  simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hdispatch,
    ReferenceActivePhysicalStep.dispatch, hfirstState, CoordinatorRoundDispatch.dispatch] at hbirth
  cases hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput
        (ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h hc hs).input) with
  | choiceDomainFailure installed =>
      simp only [hchosen] at hbirth
      exact False.elim hbirth
  | recorderBoundaryFailure installed =>
      simp only [hchosen] at hbirth
      exact False.elim hbirth
  | choiceRejected installed =>
      simp only [hchosen] at hbirth
      exact False.elim hbirth
  | chosen installed arm =>
      simp only [hchosen] at hbirth
      have hpayload := hbirth.1
      have hfacts := ReferenceFirstLaunchNumericalCell.first_installation_payload_facts
        rate z.val rewards C_star C_h hc hs installed arm hchosen
      intro a
      rw [hpayload]
      exact hfacts.2.1 a

private theorem sourceCell_sourceWeights_range
    (z : SourceZ rate rewards C_star C_h q t s hs)
    (k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val rewards
      C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
      (sourceCountSpan rate rewards C_star C_h q t s hs z)).length) :
    ∃ scores : Fin p.K → ℕ,
      let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
        (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
        (sourceCountSpan rate rewards C_star C_h q t s hs z) k
      ReferenceFirstWindowNumericalStream.sourceWeights cell.selected.view.payload
        cell.selected.view.complementWeights = scoreVector p scores := by
  classical
  let hc := sourceCrossing rate rewards C_star C_h q t s hs z
  let span := sourceCountSpan rate rewards C_star C_h q t s hs z
  let I := ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z.val rewards C_star C_h hc
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h
    hc (t.val - s) span k
  change ∃ scores : Fin p.K → ℕ,
    ReferenceFirstWindowNumericalStream.sourceWeights cell.selected.view.payload
      cell.selected.view.complementWeights = scoreVector p scores
  have hunit : ∀ a : Fin p.K, cell.selected.view.payload.anchor a = 1 := by
    exact sourceCell_anchor_one rate rewards C_star C_h q t s hs z k
  have htruth := ReferenceFirstWindowRecordingTruth.run_first_live_window_recording_truth
    I z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards _ (t.val - s) span
    seed.activeAtStart seed.coordinatorFirst seed.followers seed.memory seed.configuration
    seed.S_zero seed.delta_zero seed.backlog_zero seed.lastDown_none seed.unoccupied
    seed.bufferValid seed.chronologicalBuffer seed.bufferStamps seed.decoderValid k
  rcases htruth with ⟨_, _, states, memories, _, hbranch⟩
  rcases hbranch with hfirst | hcontinuing
  · rcases hfirst with ⟨installed, arm, _, _, _, selected, hselected, hselection, _⟩
    have heq : cell.selected = selected :=
      Option.some.inj (cell.selection_actual.symm.trans hselected)
    have hu : ∀ a, installed.registers.payload.anchor a = 1 := by
      simpa only [heq, hselection,
        ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
        ReferenceActivePhysicalStep.firstInput] using hunit
    rw [heq, hselection]
    exact sourceWeights_register_range installed.registers hu
  · rcases hcontinuing with
      ⟨r, q0, base, dispatched, _, continuation, arm, _, _, selected, hselected, hselection, _⟩
    have heq : cell.selected = selected :=
      Option.some.inj (cell.selection_actual.symm.trans hselected)
    have hu : ∀ a, r.payload.anchor a = 1 := by
      simpa only [heq, hselection,
        ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
        ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt] using hunit
    rw [heq, hselection]
    exact sourceWeights_register_range r hu

private def sourceRunCodes
    (z : SourceZ rate rewards C_star C_h q t s hs) :=
  (ReferenceActiveHorizonMeasurability.runObservation s (t.val - s) (by omega)
    (sourceActiveRunInput rate rewards C_star C_h q t s hs z)).2

private theorem measurable_sourceRunCodes :
    Measurable (sourceRunCodes rate rewards C_star C_h q t s hs) := by
  exact (measurable_snd.comp
    (ReferenceActiveHorizonMeasurability.measurable_runObservation s (t.val - s) (by omega))).comp
      (measurable_sourceActiveRunInput rate rewards C_star C_h q t s hs)

private theorem sourceRunCodes_eq_actual
    (z : SourceZ rate rewards C_star C_h q t s hs) :
    sourceRunCodes rate rewards C_star C_h q t s hs z =
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z.val rewards C_star C_h
        (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
        (sourceCountSpan rate rewards C_star C_h q t s hs z)).records.map
          ReferenceActiveHorizonMeasurability.roundRecordCode := by
  simp [sourceRunCodes, ReferenceActiveHorizonMeasurability.runObservation_records,
    sourceActiveRun_eq_actual]

private theorem measurable_sourceWindowLength :
    Measurable (fun z : SourceZ rate rewards C_star C_h q t s hs =>
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val rewards C_star C_h
        (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
        (sourceCountSpan rate rewards C_star C_h q t s hs z)).length) := by
  let flags (z : SourceZ rate rewards C_star C_h q t s hs) : Fin (t.val - s) → Bool :=
    fun k =>
      (ReferenceActiveHorizonMeasurability.listObservationAt
        (sourceRunCodes rate rewards C_star C_h q t s hs z) k.val).elim
        (fun _ => false) cutoffRecordCode
  have hcoords := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
    (measurable_sourceRunCodes rate rewards C_star C_h q t s hs)
  have hflags : Measurable flags := by
    apply measurable_pi_iff.mpr
    intro k
    have htag := (measurable_pi_apply k.val).comp (measurable_snd.comp hcoords)
    have hclassify : Measurable
        (fun tagged : Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode
          (p := p) (rate := rate) => tagged.elim (fun _ => false) cutoffRecordCode) :=
      Measurable.sumElim measurable_const measurable_cutoffRecordCode
    exact hclassify.comp htag
  let f (v : Fin (t.val - s) → Bool) := ((List.ofFn v).takeWhile (! ·)).length
  have hf : Measurable f := measurable_of_countable _
  have hm := hf.comp hflags
  convert hm using 1
  funext z
  let codes := sourceRunCodes rate rewards C_star C_h q t s hs z
  let run := ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z.val rewards C_star C_h
    (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
    (sourceCountSpan rate rewards C_star C_h q t s hs z)
  have hlength : codes.length = t.val - s := by
    dsimp [codes, sourceRunCodes]
    exact ReferenceActiveHorizonMeasurability.runObservation_recordCount s (t.val - s) (by omega)
      (sourceActiveRunInput rate rewards C_star C_h q t s hs z)
  have hlist : List.ofFn (flags z) = codes.map cutoffRecordCode := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map, hlength]
    · intro j hj₁ hj₂
      simp only [List.getElem_ofFn, List.getElem_map]
      dsimp [flags]
      unfold ReferenceActiveHorizonMeasurability.listObservationAt
      have hj : j < codes.length := by simpa [hlength] using hj₁
      rw [List.getElem?_eq_getElem hj]
      rfl
  have htags : codes.map cutoffRecordCode =
      run.records.map (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) := by
    dsimp [codes, run]
    rw [sourceRunCodes_eq_actual]
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro record hrecord
    exact cutoffRecordCode_roundRecordCode record
  change (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val rewards C_star C_h
      (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
      (sourceCountSpan rate rewards C_star C_h q t s hs z)).length =
    ((List.ofFn (flags z)).takeWhile (! ·)).length
  rw [hlist, htags]
  have hrunEq : run = ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z.val rewards
      C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
      (sourceCountSpan rate rewards C_star C_h q t s hs z) := rfl
  unfold ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    ReferenceFirstLiveConfirmationHistory.firstLiveWindow
  rw [← hrunEq]
  simp only [List.takeWhile_map, List.length_map, Function.comp_def]

private noncomputable def extendSubtype {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (s : Set X) (f : s → Y) (y₀ : Y) : X → Y := by
  classical
  exact fun x => if h : x ∈ s then f ⟨x, h⟩ else y₀

private theorem measurable_extendSubtype {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (s : Set X) (hs : MeasurableSet s)
    (f : s → Y) (hf : Measurable f) (y₀ : Y) :
    Measurable (extendSubtype s f y₀) := by
  classical
  intro u hu
  have himage : MeasurableSet (((↑) : s → X) '' (f ⁻¹' u)) :=
    (MeasurableEmbedding.subtype_coe hs).measurableSet_image' (hf hu)
  have houtside : MeasurableSet (if y₀ ∈ u then sᶜ else ∅) := by
    split_ifs with hy
    · exact hs.compl
    · exact MeasurableSet.empty
  have heq : {x | extendSubtype s f y₀ x ∈ u} =
      (((↑) : s → X) '' (f ⁻¹' u)) ∪ (if y₀ ∈ u then sᶜ else ∅) := by
    ext x
    by_cases hx : x ∈ s <;> simp [extendSubtype, hx, Set.mem_image]
  change MeasurableSet {x | extendSubtype s f y₀ x ∈ u}
  rw [heq]
  exact himage.union houtside

/-- The finite numerical readout is Borel on the original count-`n` source
stratum. Every coordinate is tagged absent exactly when the actual first-live
window has no record there. -/
theorem measurable_numericalCountPastReadout
    (control0 : TimeControl p) :
    Measurable (numericalCountPastReadout rate rewards C_star C_h q t s hs control0) := by
  classical
  let window (z : SourceZ rate rewards C_star C_h q t s hs) :=
    ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val rewards C_star C_h
      (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
      (sourceCountSpan rate rewards C_star C_h q t s hs z)
  have hwindowLength : Measurable (fun z : SourceZ rate rewards C_star C_h q t s hs =>
      (window z).length) := by
    convert measurable_sourceWindowLength rate rewards C_star C_h q t s hs using 1
  let coordinate (k : Fin (t.val - s))
      (z : SourceZ rate rewards C_star C_h q t s hs) : Unit ⊕ NumericalCellReadout p :=
    if h : k.val < (window z).length then
      let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards
        C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
        (sourceCountSpan rate rewards C_star C_h q t s hs z) ⟨k.val, h⟩
      Sum.inr (cell.input.enabled, (cell.input.recordedArm, (cell.input.reward, cell.input.rate)))
    else Sum.inl ()
  have hcoordinate (k : Fin (t.val - s)) : Measurable (coordinate k) := by
    let present : Set (SourceZ rate rewards C_star C_h q t s hs) :=
      {z | k.val < (window z).length}
    let record (x : present) : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
      (window x.val)[k.val]'x.property
    let cell (x : present) :=
      ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate x.val.val rewards C_star C_h
        (sourceCrossing rate rewards C_star C_h q t s hs x.val) (t.val - s)
        (sourceCountSpan rate rewards C_star C_h q t s hs x.val) ⟨k.val, x.property⟩
    have hpresent : MeasurableSet present := measurableSet_lt measurable_const hwindowLength
    have hinputEq (x : present) : (record x).input =
        runPrefixInput (rate := rate) (t := t) (s := s) s k.val (by omega)
          (sourceActiveRunInput rate rewards C_star C_h q t s hs x.val) := by
      let run := ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate x.val.val rewards
        C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs x.val) (t.val - s)
        (sourceCountSpan rate rewards C_star C_h q t s hs x.val)
      have hprefix : window x.val <+: run.records := by
        dsimp [window, run, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow]
        exact List.takeWhile_prefix _
      have hfull : k.val < run.records.length := lt_of_lt_of_le x.property hprefix.length_le
      have hget : (record x) = run.records[k.val]'hfull := hprefix.getElem x.property
      have hbuilt := List.getElem_of_eq
        (sourceRunRecords_eq_ofFn rate rewards C_star C_h q t s hs x.val) hfull
      have hbuilt' : run.records[k.val]'hfull =
          (⟨runPrefixInput (rate := rate) (t := t) (s := s) s k.val (by omega)
              (sourceActiveRunInput rate rewards C_star C_h q t s hs x.val),
            ReferenceActivePhysicalStep.step
              (runPrefixInput (rate := rate) (t := t) (s := s) s k.val (by omega)
                (sourceActiveRunInput rate rewards C_star C_h q t s hs x.val)), rfl⟩ :
            ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) := by
        simpa only [List.getElem_ofFn] using hbuilt
      have hrecord : record x =
          (⟨runPrefixInput (rate := rate) (t := t) (s := s) s k.val (by omega)
              (sourceActiveRunInput rate rewards C_star C_h q t s hs x.val),
            ReferenceActivePhysicalStep.step
              (runPrefixInput (rate := rate) (t := t) (s := s) s k.val (by omega)
                (sourceActiveRunInput rate rewards C_star C_h q t s hs x.val)), rfl⟩ :
            ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :=
        hget.trans hbuilt'
      exact congrArg ReferenceActivePhysicalHorizon.RoundRecord.input hrecord
    have hinput : Measurable (fun x : present => (record x).input) := by
      have hactive : Measurable (fun x : present =>
          sourceActiveRunInput rate rewards C_star C_h q t s hs x.val) :=
        (measurable_sourceActiveRunInput rate rewards C_star C_h q t s hs).comp
          measurable_subtype_coe
      have hprefixInput : Measurable (fun x : present =>
          runPrefixInput (rate := rate) (t := t) (s := s) s k.val (by omega)
            (sourceActiveRunInput rate rewards C_star C_h q t s hs x.val)) :=
        (measurable_runPrefixInput (rate := rate) (t := t) (s := s)
          s k.val (by omega)).comp hactive
      have heq : (fun x : present => (record x).input) =
          fun x => runPrefixInput (rate := rate) (t := t) (s := s) s k.val (by omega)
            (sourceActiveRunInput rate rewards C_star C_h q t s hs x.val) := funext hinputEq
      rw [heq]
      exact hprefixInput
    have hunit : ∀ x a, (cell x).selected.view.payload.anchor a = 1 := by
      intro x a
      exact sourceCell_anchor_one rate rewards C_star C_h q t s hs x.val
        ⟨k.val, x.property⟩ a
    have hscore : ∀ x, ∃ scores : Fin p.K → ℕ,
        ReferenceFirstWindowNumericalStream.sourceWeights (cell x).selected.view.payload
          (cell x).selected.view.complementWeights = scoreVector p scores := by
      intro x
      exact sourceCell_sourceWeights_range rate rewards C_star C_h q t s hs x.val
        ⟨k.val, x.property⟩
    have hfield : Measurable (fun x : present =>
        ((cell x).input.enabled, ((cell x).input.recordedArm,
          ((cell x).input.reward, (cell x).input.rate)))) :=
      measurable_cell_readout record cell hinput hunit hscore
    let defaultField : NumericalCellReadout p := (false, (none, (fun _ => 0, fun _ => 0)))
    let fieldExt := extendSubtype present (fun x : present =>
      ((cell x).input.enabled, ((cell x).input.recordedArm,
        ((cell x).input.reward, (cell x).input.rate)))) defaultField
    have hfieldExt : Measurable fieldExt :=
      measurable_extendSubtype present hpresent _ hfield defaultField
    have hresult : Measurable (fun z : SourceZ rate rewards C_star C_h q t s hs =>
        if h : z ∈ present then Sum.inr (fieldExt z) else Sum.inl ()) :=
      Measurable.ite hpresent (measurable_inr.comp hfieldExt) measurable_const
    convert hresult using 1
    funext z
    by_cases hcond : k.val < (window z).length
    · have hz : z ∈ present := by simpa [present] using hcond
      simp [coordinate, present, fieldExt, extendSubtype, defaultField, cell, hz, hcond]
    · have hz : z ∉ present := by simpa [present] using hcond
      simp [coordinate, present, hz, hcond]
  have hcoordinate : Measurable (fun z : SourceZ rate rewards C_star C_h q t s hs =>
      fun k : Fin (t.val - s) => coordinate k z) := by
    apply measurable_pi_iff.mpr
    intro k
    exact hcoordinate k
  convert hcoordinate using 1
  funext z
  funext k
  have hcellLength := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
    rate z.val rewards C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs z)
    (t.val - s) (sourceCountSpan rate rewards C_star C_h q t s hs z)
  by_cases hk : k.val < (window z).length
  ·
    have hkCells : k.val < (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z.val rewards C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs z)
        (t.val - s) (sourceCountSpan rate rewards C_star C_h q t s hs z)).length := by
      rw [hcellLength]
      exact hk
    simp only [coordinate, dite_eq_left hk, numericalCountPastReadout]
    rw [List.getElem?_eq_getElem hkCells,
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get rate z.val rewards
        C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs z) (t.val - s)
        (sourceCountSpan rate rewards C_star C_h q t s hs z)
        ⟨k.val, hk⟩]
  · have hkCells : (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z.val rewards C_star C_h (sourceCrossing rate rewards C_star C_h q t s hs z)
        (t.val - s) (sourceCountSpan rate rewards C_star C_h q t s hs z)).length ≤ k.val := by
      calc
        _ = (window z).length := hcellLength
        _ ≤ k.val := Nat.le_of_not_gt hk
    simp only [coordinate, dite_eq_right hk, numericalCountPastReadout]
    rw [List.getElem?_eq_none hkCells]


end Bandits.Support.ReferenceFirstLiveNumericalPrefixBorel

end
