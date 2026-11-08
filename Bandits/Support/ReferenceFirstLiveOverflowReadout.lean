/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpFalseTail
public import Bandits.Support.ReferenceFirstLiveStoppedQueueComparison

import Lean.Elab.Tactic.Omega

/-!
# Inclusive overflow readouts of the actual first-live window

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`05_binary_transport.tex:354-431`, `06_interruptions.tex:246-296,355-408`,
`08_main_theorem.tex:29-42`, and `appendix_a_local_protocol.tex:28-64`.

All lists below come from the original source and corrected launch. The
overflow search is restricted to the first live window, which excludes the
chosen cutoff round. Its crossing update and every diagnostic in that round
are retained. Absence of a crossing here says nothing about later windows.
These are internal readouts, not a global stopping time or a probability law.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstLiveOverflowReadout

open ConstructorDimensions
open MeasureTheory

universe u


variable {p : Parameters}

/-- Numerical fields retain their ordinary finite/product Borel spaces. -/
abbrev NumericalCellReadout (p : Parameters) :=
  Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ)))

private def numericalArrivalReadout (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : NumericalCellReadout p) : Bool × (Fin p.K → ℕ) :=
  (z.1, fun a => if z.2.1 = some a then Nat.floor ((rate.n : ℝ) * z.2.2.1 a / z.2.2.2 a) else 0)

private theorem measurable_numericalArrivalReadout (rate : ReferenceActivePhysicalStep.RateInput p) :
    Measurable (numericalArrivalReadout rate) := by
  classical
  apply Measurable.prodMk measurable_fst
  apply measurable_pi_iff.mpr
  intro a
  have hy : Measurable (fun z : NumericalCellReadout p =>
      Nat.floor ((rate.n : ℝ) * z.2.2.1 a / z.2.2.2 a)) := by fun_prop
  have hm : MeasurableSet {z : NumericalCellReadout p | z.2.1 = some a} :=
    (measurableSet_singleton (some a)).preimage (measurable_fst.comp measurable_snd)
  exact hy.ite hm measurable_const

/-- The whole numerical input is fixed by actual selection and ordinary
constructor injectivity. In particular, no measurability of choice is used. -/
theorem actualLiveSourceCell_input_unique
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (a b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record) : a.input = b.input := by
  have hselected : a.selected = b.selected :=
    Option.some.inj (a.selection_actual.symm.trans b.selection_actual)
  have hstates : a.states = b.states := by
    funext i
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((a.ordinary i).symm.trans (b.ordinary i))).1
  cases a
  cases b
  dsimp only at hselected hstates ⊢
  cases hselected
  cases hstates
  simp_all only

private def outcomeIsCutoff : ReferenceLiveDispatchOutputMeasurability.OutcomeData p → Bool
  | .cutoffChosen _ _ _ => true
  | _ => false

private theorem measurable_cutoffChosen
    {rate : ReferenceActivePhysicalStep.RateInput p} :
    Measurable (ReferenceCollectionPhaseHistory.cutoffChosen (p := p) (rate := rate)) := by
  apply measurable_of_restrict_of_restrict_compl
    ReferenceFirstLiveCoordinatorStepMeasurability.measurableSet_liveSet
  · have htag : Measurable (outcomeIsCutoff (p := p)) := measurable_of_countable _
    have h := htag.comp
      (ReferenceLiveDispatchOutputMeasurability.measurable_dispatchLive_outcomeData.comp
        (ReferenceFirstLiveCoordinatorStepMeasurability.measurable_liveCoordinates
          (p := p) (rate := rate)))
    convert h using 1
    funext x
    dsimp only [Function.comp_def, Set.domRestrict,
      ReferenceFirstLiveCoordinatorStepMeasurability.liveCoordinates]
    rw [ReferenceLiveDispatchOutputMeasurability.outcomeData_originalInput]
    unfold ReferenceCollectionPhaseHistory.cutoffChosen ReferenceActivePhysicalStep.prepare
    dsimp only
    rw [ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction
      x.val _ _ _ (ReferenceFirstLiveCoordinatorStepMeasurability.live_state x)]
    cases CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x.val
      (ReferenceFirstLiveCoordinatorStepMeasurability.liveRegisters x)
      (ReferenceFirstLiveCoordinatorStepMeasurability.liveOwned x)
      (ReferenceFirstLiveCoordinatorStepMeasurability.liveBase x)) <;> rfl
  · have heq : (fun x : ↥((ReferenceFirstLiveCoordinatorStepMeasurability.liveSet
        (p := p) (rate := rate))ᶜ) => ReferenceCollectionPhaseHistory.cutoffChosen x.val) =
        fun _ => false := by
      funext x
      cases hc : x.val.state.coordinator with
      | first =>
          simp only [ReferenceCollectionPhaseHistory.cutoffChosen,
            ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
            hc, CoordinatorRoundDispatch.dispatch]
          rfl
      | live r q base =>
          exfalso
          exact x.property ⟨(r.payload,
            ReferenceActivePhysicalStepMeasurability.encodeLive r q base), by
              simp only [ReferenceActivePhysicalStepMeasurability.encodeState,
                hc, ReferenceActivePhysicalStepMeasurability.encodeCoordinator]⟩
      | collection payload ledger proposal =>
          simp only [ReferenceCollectionPhaseHistory.cutoffChosen,
            ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
            hc, CoordinatorRoundDispatch.dispatch]
          by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
          · simp only [hcut, and_self, dite_true]
            rfl
          · simp only [hcut, dite_false]
      | dagger =>
          simp only [ReferenceCollectionPhaseHistory.cutoffChosen,
            ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch, hc]
    change Measurable (fun x : ↥((ReferenceFirstLiveCoordinatorStepMeasurability.liveSet
      (p := p) (rate := rate))ᶜ) => ReferenceCollectionPhaseHistory.cutoffChosen x.val)
    rw [heq]
    exact measurable_const

private theorem measurable_of_inr {X α : Type*} [MeasurableSpace X] [MeasurableSpace α]
    (f : X → α) (hf : Measurable (fun x => (Sum.inr (f x) : Unit ⊕ α))) :
    Measurable f := by
  intro u hu
  convert hf hu.inr_image using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Sum.inr.injEq, exists_eq_right]

private theorem measurable_list_take {X α : Type*} [MeasurableSpace X] [MeasurableSpace α]
    (records : X → List α) (hrecords : Measurable records)
    (n : X → ℕ) (hn : Measurable n) :
    Measurable (fun x => (records x).take (n x)) := by
  classical
  have hc := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hrecords
  have hlen : Measurable (fun x => min (n x) (records x).length) :=
    (measurable_of_countable (fun v : ℕ × ℕ => min v.1 v.2)).comp
      (hn.prodMk (measurable_fst.comp hc))
  have ht : Measurable (fun x => fun j =>
      ReferenceActiveHorizonMeasurability.listObservationAt ((records x).take (n x)) j) := by
    apply measurable_pi_iff.mpr
    intro j
    have htag := (measurable_pi_apply j).comp (measurable_snd.comp hc)
    have h : Measurable (fun x => if j < n x then
        ReferenceActiveHorizonMeasurability.listObservationAt (records x) j
        else (Sum.inl () : Unit ⊕ α)) :=
      htag.ite (measurableSet_lt (measurable_const (a := j)) hn) measurable_const
    convert h using 1
    funext x
    unfold ReferenceActiveHorizonMeasurability.listObservationAt
    rw [List.getElem?_take]
    by_cases hj : j < n x
    · simp only [hj, ite_true]
    · simp only [hj, ite_false]
  apply measurable_comap_iff.mpr
  convert hlen.prodMk ht using 1
  funext x
  exact Prod.ext List.length_take rfl

private theorem measurable_of_some {X : Type*} {α : Type u} [MeasurableSpace X] [MeasurableSpace α]
    (f : X → α) (hf : Measurable (fun x => some (f x))) : Measurable f := by
  let e : Option α ≃ α ⊕ PUnit.{u + 1} := Equiv.optionEquivSumPUnit.{u, u} α
  have hs : Measurable (fun x => e (some (f x))) := measurable_comap_iff.mp hf
  intro u hu
  convert hs hu.inl_image using 1
  ext x
  change f x ∈ u ↔ (Sum.inl (f x) : α ⊕ PUnit.{u + 1}) ∈ Sum.inl '' u
  simp only [Set.mem_image, Sum.inl.injEq, exists_eq_right]

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

section Fiber

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (s count : ℕ) (hspan : s + count ≤ p.T)

/-- The genuine generated-launch fibre, with its inherited measurable space. -/
abbrev LaunchFiber := ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber (rate := rate) rewards C_star C_h s

/-- The crossing is produced from membership in the genuine launch fibre. -/
theorem launch_crossing (x : LaunchFiber rate rewards C_star C_h s) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)).crossing.isSome = true :=
  x.property.1

/-- The elapsed time is produced from the same fibre membership. -/
theorem launch_elapsed (x : LaunchFiber rate rewards C_star C_h s) :
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)).completed = s :=
  x.property.2

include hspan in
theorem launch_span (x : LaunchFiber rate rewards C_star C_h s) :
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)).completed +
      count ≤ p.T := by
  rw [launch_elapsed rate rewards C_star C_h s x]
  exact hspan

/-- Literal actual first-live records, including all same-round diagnostics. -/
def firstLiveWindow (x : LaunchFiber rate rewards C_star C_h s) :=
  ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate x.val rewards C_star C_h
    (launch_crossing rate rewards C_star C_h s x) count
    (launch_span rate rewards C_star C_h s count hspan x)

/-- Literal actual whole-arm numerical source cells on the same window. -/
def firstLiveCells (x : LaunchFiber rate rewards C_star C_h s) :=
  ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate x.val rewards C_star C_h
    (launch_crossing rate rewards C_star C_h s x) count
    (launch_span rate rewards C_star C_h s count hspan x)

def firstLiveLength (x : LaunchFiber rate rewards C_star C_h s) : ℕ :=
  (firstLiveWindow rate rewards C_star C_h s count hspan x).length

def firstLiveCellReadout (x : LaunchFiber rate rewards C_star C_h s) :
    List (NumericalCellReadout p) :=
  (firstLiveCells rate rewards C_star C_h s count hspan x).map
    (fun c => (c.enabled, (c.recordedArm, (c.reward, c.rate))))

def firstLiveOverflowPrefix (x : LaunchFiber rate rewards C_star C_h s) : ℕ :=
  UnstoppedRecordedQueueComparison.firstOverflowPrefix (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (firstLiveCells rate rewards C_star C_h s count hspan x)

def firstLiveInclusiveCount (x : LaunchFiber rate rewards C_star C_h s) : ℕ :=
  min (firstLiveLength rate rewards C_star C_h s count hspan x)
    (firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x)

def firstLiveInclusiveRecords (x : LaunchFiber rate rewards C_star C_h s) :=
  (firstLiveWindow rate rewards C_star C_h s count hspan x).take
    (firstLiveInclusiveCount rate rewards C_star C_h s count hspan x)

def firstLiveInclusiveCensus (x : LaunchFiber rate rewards C_star C_h s) :
    List (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :=
  (firstLiveInclusiveRecords rate rewards C_star C_h s count hspan x).map ReferenceActiveHorizonMeasurability.roundRecordCode

/-- Physical rounds are one-based; the retained `Fin T` input is zero-based. -/
def firstLiveOverflowRound (x : LaunchFiber rate rewards C_star C_h s) : Option ℕ :=
  if firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x ≤
      firstLiveLength rate rewards C_star C_h s count hspan x then
    some (s + firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x)
  else none

theorem firstLiveCells_length (x : LaunchFiber rate rewards C_star C_h s) :
    (firstLiveCells rate rewards C_star C_h s count hspan x).length =
      firstLiveLength rate rewards C_star C_h s count hspan x :=
  ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length rate x.val rewards C_star C_h
    (launch_crossing rate rewards C_star C_h s x) count
    (launch_span rate rewards C_star C_h s count hspan x)

theorem firstLiveOverflowPrefix_pos (x : LaunchFiber rate rewards C_star C_h s) :
    0 < firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x :=
  UnstoppedRecordedQueueComparison.first_overflow_prefix_pos _ _

/-- Exact first strict post-update crossing, with every earlier prefix safe. -/
theorem firstLiveOverflowRound_spec (x : LaunchFiber rate rewards C_star C_h s) (v : ℕ) :
    firstLiveOverflowRound rate rewards C_star C_h s count hspan x = some v ↔
      ∃ k, 1 ≤ k ∧ k ≤ firstLiveLength rate rewards C_star C_h s count hspan x ∧
        v = s + k ∧
        UnstoppedRecordedQueueComparison.replay_crosses_overflow (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (firstLiveCells rate rewards C_star C_h s count hspan x) k ∧
        ∀ j, 1 ≤ j → j < k →
          ¬ UnstoppedRecordedQueueComparison.replay_crosses_overflow (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (firstLiveCells rate rewards C_star C_h s count hspan x) j := by
  classical
  let cells := firstLiveCells rate rewards C_star C_h s count hspan x
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let kappa := firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x
  have hlen : cells.length = firstLiveLength rate rewards C_star C_h s count hspan x :=
    firstLiveCells_length rate rewards C_star C_h s count hspan x
  have hpos := firstLiveOverflowPrefix_pos rate rewards C_star C_h s count hspan x
  constructor
  · intro hv
    unfold firstLiveOverflowRound at hv
    split at hv
    next hk =>
      refine ⟨kappa, hpos, hk, (Option.some.inj hv).symm, ?_, ?_⟩
      · apply UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first q cells
        change kappa ≤ cells.length
        rw [hlen]
        exact hk
      · intro j hj hjk
        exact UnstoppedRecordedQueueComparison.not_replay_crosses_overflow_before_first q cells j hj
          (by omega) hjk
    next hk => contradiction
  · rintro ⟨k, hkpos, hkle, hv, hcross, hbefore⟩
    have hex : ∃ n, 1 ≤ n ∧ n ≤ cells.length ∧ UnstoppedRecordedQueueComparison.replay_crosses_overflow q cells n :=
      ⟨k, hkpos, by omega, hcross⟩
    have hkmin : kappa ≤ k := by
      change UnstoppedRecordedQueueComparison.firstOverflowPrefix q cells ≤ k
      rw [UnstoppedRecordedQueueComparison.firstOverflowPrefix, dite_eq_left hex]
      exact Nat.find_min' hex ⟨hkpos, by omega, hcross⟩
    have heq : kappa = k := by
      by_contra hne
      have hlt : kappa < k := by omega
      exact hbefore kappa hpos hlt
        (UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first q cells (by
          change kappa ≤ cells.length
          omega))
    simp only [firstLiveOverflowRound, ← hv, show
      firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x = k from heq,
      ite_eq_left hkle]

theorem firstLiveInclusiveCensus_length (x : LaunchFiber rate rewards C_star C_h s) :
    (firstLiveInclusiveCensus rate rewards C_star C_h s count hspan x).length =
      firstLiveInclusiveCount rate rewards C_star C_h s count hspan x := by
  simp only [firstLiveInclusiveCensus, List.length_map, firstLiveInclusiveRecords,
    List.length_take, firstLiveInclusiveCount, firstLiveLength]
  omega

/-- The census keeps the literal indexed record code; no diagnostic filter is applied. -/
theorem firstLiveInclusiveCensus_indexed (x : LaunchFiber rate rewards C_star C_h s)
    (j : ℕ) (hj : j < firstLiveInclusiveCount rate rewards C_star C_h s count hspan x) :
    (firstLiveInclusiveCensus rate rewards C_star C_h s count hspan x)[j]'
      (by rw [firstLiveInclusiveCensus_length]; exact hj) =
      ReferenceActiveHorizonMeasurability.roundRecordCode ((firstLiveWindow rate rewards C_star C_h s count hspan x)[j]'
        (by have := Nat.min_le_left
              (firstLiveLength rate rewards C_star C_h s count hspan x)
              (firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x)
            exact hj.trans_le this)) := by
  simp only [firstLiveInclusiveCensus, firstLiveInclusiveRecords,
    List.getElem_map, List.getElem_take]

theorem firstLiveInclusiveCensus_absent (x : LaunchFiber rate rewards C_star C_h s)
    (j : ℕ) (hj : firstLiveInclusiveCount rate rewards C_star C_h s count hspan x ≤ j) :
    (firstLiveInclusiveCensus rate rewards C_star C_h s count hspan x)[j]? = none := by
  exact List.getElem?_eq_none (by rw [firstLiveInclusiveCensus_length]; exact hj)

/-- The whole crossing record remains present, including its UP and DOWN diagnostics. -/
theorem firstLive_crossing_record_included (x : LaunchFiber rate rewards C_star C_h s)
    (hk : firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x ≤
      firstLiveLength rate rewards C_star C_h s count hspan x) :
    let k := firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x
    ∃ hj : k - 1 < (firstLiveWindow rate rewards C_star C_h s count hspan x).length,
      (firstLiveInclusiveRecords rate rewards C_star C_h s count hspan x)[k - 1]? =
        some ((firstLiveWindow rate rewards C_star C_h s count hspan x)[k - 1]'hj) := by
  dsimp only
  have hpos := firstLiveOverflowPrefix_pos rate rewards C_star C_h s count hspan x
  have hj : firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x - 1 <
      (firstLiveWindow rate rewards C_star C_h s count hspan x).length := by
    change _ < firstLiveLength rate rewards C_star C_h s count hspan x
    omega
  refine ⟨hj, ?_⟩
  rw [firstLiveInclusiveRecords, List.getElem?_take_of_lt]
  · exact List.getElem?_eq_getElem hj
  · simp only [firstLiveInclusiveCount, Nat.min_eq_right hk]
    omega


private theorem firstLive_selected_anchor_one
    (x : LaunchFiber rate rewards C_star C_h s)
    (k : Fin (firstLiveWindow rate rewards C_star C_h s count hspan x).length) :
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate x.val rewards C_star C_h (launch_crossing rate rewards C_star C_h s x) count
      (launch_span rate rewards C_star C_h s count hspan x) k
    ∀ a : Fin p.K, cell.selected.view.payload.anchor a = 1 := by
  dsimp only
  let hc := launch_crossing rate rewards C_star C_h s x
  let span := launch_span rate rewards C_star C_h s count hspan x
  let I := ReferenceFirstLaunchNumericalCell.launchState rate x.val rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate x.val rewards C_star C_h hc
  let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate x.val rewards C_star C_h hc count span
  let W := firstLiveWindow rate rewards C_star C_h s count hspan x
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate x.val rewards C_star C_h hc count span k
  have hbirth := ReferenceFirstDownRecoveryBudget.run_first_selected_payload I x.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards _ count span
    seed.activeAtStart seed.coordinatorFirst k cell.selected cell.selection_actual
  obtain ⟨birth, hmem, htime, hbirth, _⟩ := hbirth
  have hcount : 0 < count := by
    have hw : W.IsPrefix E.records := List.takeWhile_prefix _
    have hlen : E.records.length = count := ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    exact (Nat.zero_lt_of_lt k.isLt).trans_le (hw.length_le.trans_eq hlen)
  have hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)).completed < p.T := by
    have h := launch_elapsed rate rewards C_star C_h s x
    omega
  let first := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
    rate x.val rewards C_star C_h hc hs
  have hfirstMem : first ∈ E.records := by
    obtain ⟨tail, htail⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
      I x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val)
      rewards _ 1 (count - 1) (by omega) seed.activeAtStart
    have htail' : E.records =
        (ReferenceFirstLaunchNumericalCell.firstPhysicalRun
          rate x.val rewards C_star C_h hc hs).records ++ tail := by
      simpa only [E, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
        ReferenceFirstLaunchNumericalCell.firstPhysicalRun, I, Nat.add_sub_of_le hcount] using htail
    rw [htail', ReferenceFirstLaunchNumericalCell.firstPhysicalRun_records]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  have hfirstInputs := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord_source_inputs
    rate x.val rewards C_star C_h hc hs
  have heq : birth = first := ReferenceAssignmentPayloadChronology.run_records_time_injective
    I x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val)
    rewards _ count span seed.activeAtStart hmem hfirstMem
    (htime.trans hfirstInputs.2.1.symm)
  rw [heq] at hbirth
  have hdispatch : first.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch first.input := by
    rw [first.output_eq]
    rfl
  have hfirstState : first.input.state.coordinator = .first := by
    rw [hfirstInputs.1]
    exact seed.coordinatorFirst
  simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hdispatch,
    ReferenceActivePhysicalStep.dispatch, hfirstState, CoordinatorRoundDispatch.dispatch] at hbirth
  cases hchosen : CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput first.input) with
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
        rate x.val rewards C_star C_h hc hs installed arm hchosen
      intro a
      rw [hpayload]
      exact hfacts.2.1 a

private theorem firstLive_sourceWeights_range
    (x : LaunchFiber rate rewards C_star C_h s)
    (k : Fin (firstLiveWindow rate rewards C_star C_h s count hspan x).length) :
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate x.val rewards C_star C_h (launch_crossing rate rewards C_star C_h s x) count
      (launch_span rate rewards C_star C_h s count hspan x) k
    ∃ scores : Fin p.K → ℕ,
      ReferenceFirstWindowNumericalStream.sourceWeights cell.selected.view.payload
        cell.selected.view.complementWeights = scoreVector p scores := by
  dsimp only
  let hc := launch_crossing rate rewards C_star C_h s x
  let span := launch_span rate rewards C_star C_h s count hspan x
  let I := ReferenceFirstLaunchNumericalCell.launchState rate x.val rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate x.val rewards C_star C_h hc
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate x.val rewards C_star C_h hc count span k
  change ∃ scores : Fin p.K → ℕ,
    ReferenceFirstWindowNumericalStream.sourceWeights cell.selected.view.payload
      cell.selected.view.complementWeights = scoreVector p scores
  have hunit : ∀ a : Fin p.K, cell.selected.view.payload.anchor a = 1 :=
    firstLive_selected_anchor_one rate rewards C_star C_h s count hspan x k
  have htruth := ReferenceFirstWindowRecordingTruth.run_first_live_window_recording_truth
    I x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards _ count span
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
      ⟨r, q, base, dispatched, _, continuation, arm, _, _, selected, hselected, hselection, _⟩
    have heq : cell.selected = selected :=
      Option.some.inj (cell.selection_actual.symm.trans hselected)
    have hu : ∀ a, r.payload.anchor a = 1 := by
      simpa only [heq, hselection,
        ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
        ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.liveRegistersAt] using hunit
    rw [heq, hselection]
    exact sourceWeights_register_range r hu

/-- The actual launch getter and the generated adapter select the same state. -/
theorem actualFirstLiveRun_eq_generated
    (x : LaunchFiber rate rewards C_star C_h s) :
    ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate x.val rewards C_star C_h
      (launch_crossing rate rewards C_star C_h s x) count
      (launch_span rate rewards C_star C_h s count hspan x) =
      ReferenceActiveHorizonMeasurability.runOfInput s count hspan
        (ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
          (rate := rate) rewards C_star C_h s x) := by
  have hstate : ReferenceFirstLaunchNumericalCell.launchState rate x.val rewards C_star C_h
      (launch_crossing rate rewards C_star C_h s x) =
      (ReferenceGeneratedDownAmbiguityMeasurability.generatedActiveRunInput
        (rate := rate) rewards C_star C_h s x).val.1 := by
    exact Option.some.inj
      ((ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate x.val rewards C_star C_h (launch_crossing rate rewards C_star C_h s x)).symm.trans
        (ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
          rate x.val rewards C_star C_h
          (ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunch_ne_none
            (rate := rate) rewards C_star C_h s x)))
  unfold ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    ReferenceActiveHorizonMeasurability.runOfInput
  simp only [launch_elapsed rate rewards C_star C_h s x]
  rfl

/-- Identification with the actual complete suffix, not a supplied trace premise. -/
theorem firstLiveWindow_eq_completeSuffix_take
    (x : LaunchFiber rate rewards C_star C_h s) :
    firstLiveWindow rate rewards C_star C_h s count hspan x =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate x.val rewards C_star C_h).take count) := by
  unfold firstLiveWindow ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
  rw [actualFirstLiveRun_eq_generated rate rewards C_star C_h s count hspan x,
    ReferenceGeneratedDownAmbiguityMeasurability.generatedRun_records_eq_completeSuffixRecords_take]

/-- Borel observations of the uncut actual run, on the original launch fibre. -/
theorem measurable_actualRunCensus :
    Measurable (fun x : LaunchFiber rate rewards C_star C_h s =>
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate x.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h s x) count
        (launch_span rate rewards C_star C_h s count hspan x)).records.map
          ReferenceActiveHorizonMeasurability.roundRecordCode) := by
  have h := (measurable_snd.comp
    (ReferenceActiveHorizonMeasurability.measurable_runObservation
      (p := p) (rate := rate) s count hspan)).comp
        (ReferenceGeneratedDownAmbiguityMeasurability.measurable_generatedActiveRunInput
          (rate := rate) rewards C_star C_h s)
  convert h using 1
  funext x
  rw [actualFirstLiveRun_eq_generated rate rewards C_star C_h s count hspan x]
  rfl

private def actualRecords (x : LaunchFiber rate rewards C_star C_h s) :=
  (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate x.val rewards C_star C_h
    (launch_crossing rate rewards C_star C_h s x) count
    (launch_span rate rewards C_star C_h s count hspan x)).records

private theorem actualRecords_length (x : LaunchFiber rate rewards C_star C_h s) :
    (actualRecords rate rewards C_star C_h s count hspan x).length = count :=
  ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _

private def actualRecordAt (j : Fin count) (x : LaunchFiber rate rewards C_star C_h s) :=
  (actualRecords rate rewards C_star C_h s count hspan x)[j.val]'
    (by rw [actualRecords_length]; exact j.isLt)

private theorem measurable_actualRecordInput (j : Fin count) :
    Measurable (fun x : LaunchFiber rate rewards C_star C_h s =>
      (actualRecordAt rate rewards C_star C_h s count hspan j x).input) := by
  have hcoords := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
    (measurable_actualRunCensus rate rewards C_star C_h s count hspan)
  have htag := (measurable_pi_apply j.val).comp (measurable_snd.comp hcoords)
  have hcode : Measurable (fun x : LaunchFiber rate rewards C_star C_h s =>
      ReferenceActiveHorizonMeasurability.roundRecordCode
        (actualRecordAt rate rewards C_star C_h s count hspan j x)) := by
    apply measurable_of_inr
    convert htag using 1
    funext x
    change Sum.inr (ReferenceActiveHorizonMeasurability.roundRecordCode
      (actualRecordAt rate rewards C_star C_h s count hspan j x)) =
      ReferenceActiveHorizonMeasurability.listObservationAt
        ((actualRecords rate rewards C_star C_h s count hspan x).map
          ReferenceActiveHorizonMeasurability.roundRecordCode) j.val
    simp only [ReferenceActiveHorizonMeasurability.listObservationAt,
      List.getElem?_map, List.getElem?_eq_getElem (show j.val <
        (actualRecords rate rewards C_star C_h s count hspan x).length by
          rw [actualRecords_length]; exact j.isLt), Option.map_some]
    rfl
  have hstate : Measurable (fun x : LaunchFiber rate rewards C_star C_h s =>
      (actualRecordAt rate rewards C_star C_h s count hspan j x).input.state) := by
    apply measurable_comap_iff.mpr
    exact (measurable_fst.comp measurable_snd).comp hcode
  have htime : Measurable (fun x : LaunchFiber rate rewards C_star C_h s =>
      (actualRecordAt rate rewards C_star C_h s count hspan j x).input.time) := by
    have hval := measurable_fst.comp hcode
    change Measurable (fun x : LaunchFiber rate rewards C_star C_h s =>
      (actualRecordAt rate rewards C_star C_h s count hspan j x).input.time.val) at hval
    apply measurable_to_countable'
    intro t
    convert (measurableSet_singleton t.val).preimage hval using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff]
  have hinputs (x : LaunchFiber rate rewards C_star C_h s) :=
    ReferenceActivePhysicalHorizon.run_record_inputs
      (ReferenceFirstLaunchNumericalCell.launchState rate x.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h s x)) x.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards _ count
      (launch_span rate rewards C_star C_h s count hspan x)
      (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate x.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h s x)).activeAtStart
      (actualRecordAt rate rewards C_star C_h s count hspan j x)
      (List.getElem_mem _)
  have hrows := (measurable_snd.comp measurable_fst).comp
    (measurable_subtype_coe : Measurable
      (fun x : LaunchFiber rate rewards C_star C_h s => x.val))
  have hselected := (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p).comp
    (measurable_subtype_coe : Measurable
      (fun x : LaunchFiber rate rewards C_star C_h s => x.val))
  have hrowsActual : Measurable (fun x : LaunchFiber rate rewards C_star C_h s =>
      (actualRecordAt rate rewards C_star C_h s count hspan j x).input.rows) := by
    have heq : (fun x : LaunchFiber rate rewards C_star C_h s =>
        (actualRecordAt rate rewards C_star C_h s count hspan j x).input.rows) =
        fun x => x.val.1.2 := funext fun x => (hinputs x).1
    rw [heq]
    exact hrows
  have hselectedActual : Measurable (fun x : LaunchFiber rate rewards C_star C_h s =>
      (actualRecordAt rate rewards C_star C_h s count hspan j x).input.selected) := by
    have heq : (fun x : LaunchFiber rate rewards C_star C_h s =>
        (actualRecordAt rate rewards C_star C_h s count hspan j x).input.selected) =
        fun x => ActualInitializationPhysicalStep.selectedRowIndex p x.val :=
      funext fun x => (hinputs x).2.1
    rw [heq]
    exact hselected
  have hrewardsActual : Measurable (fun x : LaunchFiber rate rewards C_star C_h s =>
      (actualRecordAt rate rewards C_star C_h s count hspan j x).input.rewards) := by
    have heq : (fun x : LaunchFiber rate rewards C_star C_h s =>
        (actualRecordAt rate rewards C_star C_h s count hspan j x).input.rewards) =
        fun _ => rewards := funext fun x => (hinputs x).2.2
    rw [heq]
    exact measurable_const
  apply measurable_comap_iff.mpr
  exact (hstate.prodMk (hrowsActual.prodMk (hselectedActual.prodMk
    (htime.prodMk hrewardsActual)))).subtype_mk

/-- The cutoff test uses the full dispatcher outcome tag. Successful selection
alone does not distinguish a chosen cutoff from a continuing live choice. -/
theorem measurable_firstLiveLength :
    Measurable (firstLiveLength rate rewards C_star C_h s count hspan) := by
  let flags (x : LaunchFiber rate rewards C_star C_h s) (j : Fin count) :=
    ReferenceCollectionPhaseHistory.cutoffChosen
      (actualRecordAt rate rewards C_star C_h s count hspan j x).input
  have hf : Measurable flags := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_cutoffChosen.comp
      (measurable_actualRecordInput rate rewards C_star C_h s count hspan j)
  let f (v : Fin count → Bool) := ((List.ofFn v).takeWhile (! ·)).length
  have hm : Measurable f := measurable_of_countable _
  convert hm.comp hf using 1
  funext x
  have hmap : List.ofFn (flags x) =
      (actualRecords rate rewards C_star C_h s count hspan x).map
        (fun r => ReferenceCollectionPhaseHistory.cutoffChosen r.input) := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map, actualRecords_length]
    · intro j hj hj'
      simp only [List.getElem_ofFn, List.getElem_map]
      rfl
  dsimp only [Function.comp_def, f]
  rw [hmap, List.takeWhile_map, List.length_map]
  rfl

/-- The full lossless first-live record census is Borel, with its continuous
state and saved-observation fibres retained. -/
theorem measurable_firstLiveWindowCensus :
    Measurable (fun x : LaunchFiber rate rewards C_star C_h s =>
      (firstLiveWindow rate rewards C_star C_h s count hspan x).map
        ReferenceActiveHorizonMeasurability.roundRecordCode) := by
  have h := measurable_list_take _
    (measurable_actualRunCensus rate rewards C_star C_h s count hspan)
    _ (measurable_firstLiveLength rate rewards C_star C_h s count hspan)
  convert h using 1
  funext x
  rw [← List.map_take]
  have hp : (firstLiveWindow rate rewards C_star C_h s count hspan x).IsPrefix
      (actualRecords rate rewards C_star C_h s count hspan x) := List.takeWhile_prefix _
  exact congrArg (List.map ReferenceActiveHorizonMeasurability.roundRecordCode)
    (List.prefix_iff_eq_take.mp hp)

theorem firstLiveLength_le_count (x : LaunchFiber rate rewards C_star C_h s) :
    firstLiveLength rate rewards C_star C_h s count hspan x ≤ count := by
  have hp := List.takeWhile_prefix
    (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      !ReferenceCollectionPhaseHistory.cutoffChosen r.input)
    (l := (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate x.val rewards C_star C_h
      (launch_crossing rate rewards C_star C_h s x) count
      (launch_span rate rewards C_star C_h s count hspan x)).records)
  apply hp.length_le.trans_eq
  exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _

private abbrev LiveIndexFiber (j : ℕ) :=
  {x : LaunchFiber rate rewards C_star C_h s //
    j < firstLiveLength rate rewards C_star C_h s count hspan x}

private def indexedCellReadout (j : ℕ)
    (x : LiveIndexFiber rate rewards C_star C_h s count hspan j) : NumericalCellReadout p :=
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate x.val.val rewards C_star C_h (launch_crossing rate rewards C_star C_h s x.val) count
    (launch_span rate rewards C_star C_h s count hspan x.val) ⟨j, x.property⟩
  (cell.input.enabled, (cell.input.recordedArm, (cell.input.reward, cell.input.rate)))

private theorem measurable_indexedCellReadout (j : ℕ) :
    Measurable (indexedCellReadout rate rewards C_star C_h s count hspan j) := by
  classical
  by_cases hj : j < count
  · let record (x : LiveIndexFiber rate rewards C_star C_h s count hspan j) :=
      (firstLiveWindow rate rewards C_star C_h s count hspan x.val)[j]'x.property
    let cell (x : LiveIndexFiber rate rewards C_star C_h s count hspan j) :=
      ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate x.val.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h s x.val) count
        (launch_span rate rewards C_star C_h s count hspan x.val) ⟨j, x.property⟩
    have hinput : Measurable (fun x => (record x).input) := by
      have heq : (fun x : LiveIndexFiber rate rewards C_star C_h s count hspan j => (record x).input) =
          fun x => (actualRecordAt rate rewards C_star C_h s count hspan ⟨j, hj⟩ x.val).input := by
        funext x
        have hp : (firstLiveWindow rate rewards C_star C_h s count hspan x.val).IsPrefix
            (actualRecords rate rewards C_star C_h s count hspan x.val) := List.takeWhile_prefix _
        exact congrArg (fun r => r.input) (hp.getElem x.property)
      rw [heq]
      exact (measurable_actualRecordInput rate rewards C_star C_h s count hspan ⟨j, hj⟩).comp
        measurable_subtype_coe
    exact measurable_cell_readout record cell hinput
      (fun x => firstLive_selected_anchor_one rate rewards C_star C_h s count hspan x.val ⟨j, x.property⟩)
      (fun x => firstLive_sourceWeights_range rate rewards C_star C_h s count hspan x.val ⟨j, x.property⟩)
  · have hempty : IsEmpty (LiveIndexFiber rate rewards C_star C_h s count hspan j) :=
      ⟨fun x => hj (x.property.trans_le
        (firstLiveLength_le_count rate rewards C_star C_h s count hspan x.val))⟩
    exact @measurable_of_empty _ _ _ _ hempty _

/-- The whole actual numerical cell list is Borel. The continuous reward and
rate vectors retain their product Borel structures. -/
theorem measurable_firstLiveCellReadout :
    Measurable (firstLiveCellReadout rate rewards C_star C_h s count hspan) := by
  have hlen (x : LaunchFiber rate rewards C_star C_h s) :
      (firstLiveCellReadout rate rewards C_star C_h s count hspan x).length =
        firstLiveLength rate rewards C_star C_h s count hspan x := by
    rw [firstLiveCellReadout, List.length_map, firstLiveCells_length]
  have hstream : Measurable (fun x : LaunchFiber rate rewards C_star C_h s => fun j =>
      ReferenceActiveHorizonMeasurability.listObservationAt
        (firstLiveCellReadout rate rewards C_star C_h s count hspan x) j) := by
    apply measurable_pi_iff.mpr
    intro j
    apply measurable_of_restrict_of_restrict_compl
      (measurableSet_lt (measurable_const (a := j))
        (measurable_firstLiveLength rate rewards C_star C_h s count hspan))
    · convert measurable_inr.comp
        (measurable_indexedCellReadout rate rewards C_star C_h s count hspan j) using 1
      funext x
      have hj : j < (firstLiveCellReadout rate rewards C_star C_h s count hspan x.val).length := by
        rw [hlen]
        exact x.property
      change ReferenceActiveHorizonMeasurability.listObservationAt
        (firstLiveCellReadout rate rewards C_star C_h s count hspan x.val) j =
          Sum.inr (indexedCellReadout rate rewards C_star C_h s count hspan j x)
      rw [ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_eq_getElem hj]
      simp only [firstLiveCellReadout, List.getElem_map, firstLiveCells,
        ReferenceFirstWindowNumericalStream.actualLiveSourceCells,
        List.getElem_ofFn, indexedCellReadout]
    · have heq : (fun x : {x : LaunchFiber rate rewards C_star C_h s //
          ¬ j < firstLiveLength rate rewards C_star C_h s count hspan x} =>
          ReferenceActiveHorizonMeasurability.listObservationAt
            (firstLiveCellReadout rate rewards C_star C_h s count hspan x.val) j) =
          fun _ => (Sum.inl () : Unit ⊕ NumericalCellReadout p) := by
        funext x
        have hj : (firstLiveCellReadout rate rewards C_star C_h s count hspan x.val).length ≤ j := by
          rw [hlen]
          exact Nat.le_of_not_lt x.property
        simp only [ReferenceActiveHorizonMeasurability.listObservationAt,
          List.getElem?_eq_none hj]
      change Measurable (fun x : {x : LaunchFiber rate rewards C_star C_h s //
        ¬ j < firstLiveLength rate rewards C_star C_h s count hspan x} =>
          ReferenceActiveHorizonMeasurability.listObservationAt
            (firstLiveCellReadout rate rewards C_star C_h s count hspan x.val) j)
      rw [heq]
      exact measurable_const
  apply measurable_comap_iff.mpr
  convert (measurable_firstLiveLength rate rewards C_star C_h s count hspan).prodMk hstream using 1
  funext x
  exact Prod.ext (hlen x) rfl

/-- All-arm integer arrivals are Borel before any analytical overflow cut. -/
theorem measurable_firstLiveArrivalReadout :
    Measurable (fun x : LaunchFiber rate rewards C_star C_h s =>
      (firstLiveCells rate rewards C_star C_h s count hspan x).map
        (fun c => (c.enabled, fun a => RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))) := by
  have h := ReferenceActiveHorizonMeasurability.measurable_list_map _
    (measurable_firstLiveCellReadout rate rewards C_star C_h s count hspan)
    _ (measurable_numericalArrivalReadout rate)
  convert h using 1
  funext x
  simp only [firstLiveCellReadout, List.map_map, numericalArrivalReadout,
    RecordedQueueRun.quantizedArrival, ReferenceFirstLaunchNumericalCell.queueParameters,
    Function.comp_def]

/-- Actual input time at the retained crossing record, and the corresponding
one-based physical round. -/
theorem firstLive_crossing_time (x : LaunchFiber rate rewards C_star C_h s)
    (hk : firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x ≤
      firstLiveLength rate rewards C_star C_h s count hspan x) :
    let k := firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x
    ∃ hj : k - 1 < (firstLiveWindow rate rewards C_star C_h s count hspan x).length,
      ((firstLiveWindow rate rewards C_star C_h s count hspan x)[k - 1]'hj).input.time.val =
        s + k - 1 ∧
      ((firstLiveWindow rate rewards C_star C_h s count hspan x)[k - 1]'hj).input.time.val + 1 =
        s + k ∧ s + k ≤ p.T := by
  dsimp only
  let k := firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x
  have hpos : 0 < k := firstLiveOverflowPrefix_pos rate rewards C_star C_h s count hspan x
  have hj : k - 1 < (firstLiveWindow rate rewards C_star C_h s count hspan x).length := by
    change k - 1 < firstLiveLength rate rewards C_star C_h s count hspan x
    omega
  have hcount := firstLiveLength_le_count rate rewards C_star C_h s count hspan x
  let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate x.val rewards C_star C_h
    (launch_crossing rate rewards C_star C_h s x) count
    (launch_span rate rewards C_star C_h s count hspan x)
  have hp : (firstLiveWindow rate rewards C_star C_h s count hspan x).IsPrefix E.records :=
    List.takeWhile_prefix _
  have htimes : E.records.map (fun r => r.input.time.val) =
      ReferenceActivePhysicalHorizon.calendar s count := by
    have h := ReferenceActivePhysicalHorizon.run_time_values
      (ReferenceFirstLaunchNumericalCell.launchState rate x.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h s x)) x.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards _ count
      (launch_span rate rewards C_star C_h s count hspan x)
      (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate x.val rewards C_star C_h
        (launch_crossing rate rewards C_star C_h s x)).activeAtStart
    change (ReferenceFirstWindowNumericalStream.actualFirstLiveRun _ _ _ _ _ _ _ _).records.map
      (fun r => r.input.time.val) = _
    unfold ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    simpa only [launch_elapsed rate rewards C_star C_h s x] using h
  have he : k - 1 < E.records.length := hj.trans_le hp.length_le
  have hget := congrArg (fun l : List ℕ => l[k - 1]?) htimes
  have hrecord : (firstLiveWindow rate rewards C_star C_h s count hspan x)[k - 1]'hj =
      E.records[k - 1]'he := hp.getElem hj
  have htime : ((firstLiveWindow rate rewards C_star C_h s count hspan x)[k - 1]'hj).input.time.val =
      s + (k - 1) := by
    rw [hrecord]
    simpa only [List.getElem?_map, List.getElem?_eq_getElem he,
      Option.map_some, ReferenceActivePhysicalHorizon.calendar,
      List.getElem?_range', show k - 1 < count from by omega, ite_true,
      Nat.one_mul, Option.some.injEq] using hget
  dsimp only [k] at htime hpos hj
  refine ⟨hj, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

/-- Zero requested rounds create no terminal action or numerical crossing. -/
theorem firstLive_zero (hz : count = 0)
    (x : LaunchFiber rate rewards C_star C_h s) :
    firstLiveWindow rate rewards C_star C_h s count hspan x = [] ∧
    firstLiveCells rate rewards C_star C_h s count hspan x = [] ∧
    firstLiveLength rate rewards C_star C_h s count hspan x = 0 ∧
    firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x = 1 ∧
    firstLiveInclusiveCensus rate rewards C_star C_h s count hspan x = [] ∧
    firstLiveOverflowRound rate rewards C_star C_h s count hspan x = none := by
  subst count
  have hL : firstLiveLength rate rewards C_star C_h s 0 hspan x = 0 :=
    Nat.eq_zero_of_le_zero (firstLiveLength_le_count rate rewards C_star C_h s 0 hspan x)
  have hW : firstLiveWindow rate rewards C_star C_h s 0 hspan x = [] :=
    List.length_eq_zero_iff.mp hL
  have hC : firstLiveCells rate rewards C_star C_h s 0 hspan x = [] := by
    apply List.length_eq_zero_iff.mp
    rw [firstLiveCells_length, hL]
  have hk : firstLiveOverflowPrefix rate rewards C_star C_h s 0 hspan x = 1 := by
    unfold firstLiveOverflowPrefix
    rw [hC]
    have hnone : ¬ ∃ n, 1 ≤ n ∧ n ≤ ([] : List (RecordedQueueRun.RoundInput p.K)).length ∧
        UnstoppedRecordedQueueComparison.replay_crosses_overflow
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ([] : List (RecordedQueueRun.RoundInput p.K)) n := by
      rintro ⟨n, hn, hzero, _⟩
      simp only [List.length_nil] at hzero
      omega
    rw [UnstoppedRecordedQueueComparison.firstOverflowPrefix, dite_eq_right hnone]
    rfl
  refine ⟨hW, hC, hL, hk, ?_, ?_⟩
  · simp only [firstLiveInclusiveCensus, firstLiveInclusiveRecords, hW,
      List.take_nil, List.map_nil]
  · simp only [firstLiveOverflowRound, hk, hL, Nat.reduceLeDiff, ite_false]

/-- The actual physical boundary at the inclusive numerical stopping prefix.
The before-overflow condition required by the upstream comparison is produced
by the minimum. Unoccupied local zero registers retain their virtual replay. -/
theorem firstLiveInclusive_common_boundary
    (x : LaunchFiber rate rewards C_star C_h s) :
    let b := firstLiveInclusiveCount rate rewards C_star C_h s count hspan x
    let source := x.val
    let hc := launch_crossing rate rewards C_star C_h s x
    let hspan := launch_span rate rewards C_star C_h s count hspan x
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let I := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source rewards C_star C_h hc
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan
    let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hc count hspan
    let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
    ∃ hprefix : s + b ≤ p.T,
        let boundary := ReferenceActivePhysicalHorizon.run I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
          hprefix seed.activeAtStart;
        ((b = 0 →
          boundary.finalState = I ∧ boundary.finalState.coordinator = .first ∧
          (∀ i : Fin (p.m - 1),
            ∃ sb mb, boundary.finalState.followers i = .ordinary sb mb ∧
              sb = seed.followers i ∧ mb = seed.memory i ∧
              sb.lastDown = none ∧ sb.status = .unoccupied ∧ sb.S = 0 ∧
              sb.delta = 0 ∧ sb.backlog = 0 ∧
              sb.buffer = (seed.followers i).buffer)) ∧
        (0 < b →
          ∃ r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
          ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters r,
          ∃ base : Fin (p.m - 1) → ℕ,
            boundary.finalState.coordinator = .live r owned base ∧
            r.payload.sigma.val = s ∧ r.payload.n = rate.n ∧
            (∀ i, base i = 0) ∧
            (∃ birth : ReferenceActivePhysicalHorizon.RoundRecord
                (p := p) (rate := rate),
              birth ∈ boundary.records ∧
              ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload ∧
              birth.input.time.val = s) ∧
            (∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
              (r.complementScores a, owned.queue a) =
                (RecordedQueueRun.run q (cells.take b)).registers a.1 ∧
              owned.previousService a =
                (UnstoppedRecordedQueueComparison.unstoppedReplay q cells b a.1).1 -
                  (UnstoppedRecordedQueueComparison.unstoppedReplay q cells (b - 1) a.1).1) ∧
            (∀ i : Fin (p.m - 1),
              ∃ sb mb, boundary.finalState.followers i = .ordinary sb mb ∧
                ((sb.status ≠ .unoccupied →
                  sb.lastDown = some (r.payload.downRecord i) ∧
                  (sb.S, sb.backlog) =
                    (RecordedQueueRun.run q (cells.take b)).registers
                      (r.payload.assignment.assigned i) ∧
                  sb.delta =
                    (UnstoppedRecordedQueueComparison.unstoppedReplay q cells b
                      (r.payload.assignment.assigned i)).1 -
                    (UnstoppedRecordedQueueComparison.unstoppedReplay q cells (b - 1)
                      (r.payload.assignment.assigned i)).1 ∧
                  ∃ j : Fin W.length, j.val < b ∧
                    ReferenceAcceptedUpFollowerHistory.RetainedDown W[j.val] i
                      (r.payload.downRecord i)) ∧
                (sb.status = .unoccupied →
                  sb.lastDown = none ∧ sb.S = 0 ∧ sb.delta = 0 ∧ sb.backlog = 0 ∧
                  sb.buffer = (seed.followers i).buffer ++
                    (E.records.take b).flatMap
                      (ReferenceFollowerBufferProvenance.logEmission i) ∧
                  ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                    E.records i b (r.payload.downRecord i) b =
                    ((cells.take b).map fun cell =>
                      (cell.enabled, RecordedQueueRun.quantizedArrival q cell
                        (r.payload.assignment.assigned i))) ∧
                  QueueReplay.replay (4 * rate.n) (0, 0)
                    (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                      E.records i b (r.payload.downRecord i) b) =
                    UnstoppedRecordedQueueComparison.unstoppedReplay q cells b
                      (r.payload.assignment.assigned i)))) ∧
            (∀ a : Fin p.K,
              a ∈ r.payload.slowSet.val ↔
                ∃ i : Fin (p.m - 1), r.payload.assignment.assigned i = a) ∧
            (∀ a : Fin p.K, a ∉ r.payload.slowSet.val →
              ∃ fast : CanonicalFastSampling.FastArm r.payload.slowSet, fast.1 = a))) := by
  dsimp only
  have h := ReferenceFirstLiveStoppedQueueComparison.actual_first_live_stopped_queue_common_boundary
    rate x.val rewards C_star C_h (launch_crossing rate rewards C_star C_h s x) count
    (launch_span rate rewards C_star C_h s count hspan x)
    (firstLiveInclusiveCount rate rewards C_star C_h s count hspan x)
    (Nat.min_le_left _ _)
  exact h.2.2.2.2.1 (Nat.min_le_right _ _)

/-- The actual common numerical boundary includes the crossing update. -/
theorem firstLiveInclusive_registers
    (x : LaunchFiber rate rewards C_star C_h s) (a : Fin p.K) :
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((firstLiveCells rate rewards C_star C_h s count hspan x).take
        (firstLiveInclusiveCount rate rewards C_star C_h s count hspan x))).registers a =
      UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (firstLiveCells rate rewards C_star C_h s count hspan x)
        (firstLiveInclusiveCount rate rewards C_star C_h s count hspan x) a := by
  have h := UnstoppedRecordedQueueComparison.prefix_state_comparison
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (firstLiveCells rate rewards C_star C_h s count hspan x)
    (firstLiveInclusiveCount rate rewards C_star C_h s count hspan x) (by
      rw [firstLiveCells_length]
      exact Nat.min_le_left _ _)
  simpa only [firstLiveInclusiveCount, firstLiveOverflowPrefix,
    Nat.min_assoc, Nat.min_self] using h.1 a

/-- Terminal launch fibres have zero live length and no first-live overflow. -/
theorem firstLive_terminal (hs : s = p.T)
    (x : LaunchFiber rate rewards C_star C_h s) :
    firstLiveLength rate rewards C_star C_h s count hspan x = 0 ∧
    firstLiveOverflowPrefix rate rewards C_star C_h s count hspan x = 1 ∧
    firstLiveInclusiveCensus rate rewards C_star C_h s count hspan x = [] ∧
    firstLiveOverflowRound rate rewards C_star C_h s count hspan x = none := by
  have hz : count = 0 := by omega
  have h := firstLive_zero rate rewards C_star C_h s count hspan hz x
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end Fiber

section OriginalSource

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

/-- Literal first-live segment of the whole actual physical suffix. -/
def wholeFirstLiveWindow (source : BootstrapPrivateRoundStreams.SourceInput p) :=
  ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)

/-- The empty branch is precisely actual absence of launch. A terminal
crossing uses an actual zero-length numerical stream. -/
def wholeFirstLiveCells (source : BootstrapPrivateRoundStreams.SourceInput p) :=
  if hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate source rewards C_star C_h).crossing.isSome = true then
    ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h hc
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      (by
        change ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) ≤ p.T
        exact (Nat.add_sub_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h)).le)
  else []

def wholeFirstLiveLength (source : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  (wholeFirstLiveWindow rate rewards C_star C_h source).length

def wholeFirstLiveCellReadout (source : BootstrapPrivateRoundStreams.SourceInput p) :
    List (NumericalCellReadout p) :=
  (wholeFirstLiveCells rate rewards C_star C_h source).map
    (fun c => (c.enabled, (c.recordedArm, (c.reward, c.rate))))

def wholeFirstLiveOverflowPrefix (source : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  UnstoppedRecordedQueueComparison.firstOverflowPrefix
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (wholeFirstLiveCells rate rewards C_star C_h source)

def wholeFirstLiveInclusiveCount (source : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  min (wholeFirstLiveLength rate rewards C_star C_h source)
    (wholeFirstLiveOverflowPrefix rate rewards C_star C_h source)

def wholeFirstLiveInclusiveRecords (source : BootstrapPrivateRoundStreams.SourceInput p) :=
  (wholeFirstLiveWindow rate rewards C_star C_h source).take
    (wholeFirstLiveInclusiveCount rate rewards C_star C_h source)

def wholeFirstLiveInclusiveCensus (source : BootstrapPrivateRoundStreams.SourceInput p) :=
  (wholeFirstLiveInclusiveRecords rate rewards C_star C_h source).map
    ReferenceActiveHorizonMeasurability.roundRecordCode

def wholeFirstLiveOverflowRound (source : BootstrapPrivateRoundStreams.SourceInput p) : Option ℕ :=
  if wholeFirstLiveOverflowPrefix rate rewards C_star C_h source ≤
      wholeFirstLiveLength rate rewards C_star C_h source then
    some (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
      wholeFirstLiveOverflowPrefix rate rewards C_star C_h source)
  else none

/-- A finite elapsed-time stratum includes the terminal value `T`. -/
theorem maximal_span (s : Fin (p.T + 1)) : s.val + (p.T - s.val) ≤ p.T := by
  omega

/-- Exact identification of both actual lists on each genuine launch stratum. -/
theorem wholeFirstLive_on_fiber (s : Fin (p.T + 1))
    (x : LaunchFiber rate rewards C_star C_h s.val) :
    wholeFirstLiveWindow rate rewards C_star C_h x.val =
      firstLiveWindow rate rewards C_star C_h s.val (p.T - s.val) (maximal_span s) x ∧
    wholeFirstLiveCells rate rewards C_star C_h x.val =
      firstLiveCells rate rewards C_star C_h s.val (p.T - s.val) (maximal_span s) x := by
  constructor
  · rw [firstLiveWindow_eq_completeSuffix_take]
    have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate x.val rewards C_star C_h
    rw [x.property.2] at hlen
    rw [← hlen, List.take_length]
    rfl
  · unfold wholeFirstLiveCells
    rw [dite_eq_left x.property.1]
    simp only [firstLiveCells, ← x.property.2]

/-- Every derived readout uses exactly the same stratum and calendar origin. -/
theorem wholeFirstLive_readouts_on_fiber (s : Fin (p.T + 1))
    (x : LaunchFiber rate rewards C_star C_h s.val) :
    wholeFirstLiveLength rate rewards C_star C_h x.val =
      firstLiveLength rate rewards C_star C_h s.val (p.T - s.val) (maximal_span s) x ∧
    wholeFirstLiveCellReadout rate rewards C_star C_h x.val =
      firstLiveCellReadout rate rewards C_star C_h s.val (p.T - s.val) (maximal_span s) x ∧
    wholeFirstLiveOverflowPrefix rate rewards C_star C_h x.val =
      firstLiveOverflowPrefix rate rewards C_star C_h s.val (p.T - s.val) (maximal_span s) x ∧
    wholeFirstLiveInclusiveCount rate rewards C_star C_h x.val =
      firstLiveInclusiveCount rate rewards C_star C_h s.val (p.T - s.val) (maximal_span s) x ∧
    wholeFirstLiveInclusiveCensus rate rewards C_star C_h x.val =
      firstLiveInclusiveCensus rate rewards C_star C_h s.val (p.T - s.val) (maximal_span s) x ∧
    wholeFirstLiveOverflowRound rate rewards C_star C_h x.val =
      firstLiveOverflowRound rate rewards C_star C_h s.val (p.T - s.val) (maximal_span s) x := by
  rcases wholeFirstLive_on_fiber rate rewards C_star C_h s x with ⟨hW, hC⟩
  simp only [wholeFirstLiveLength, wholeFirstLiveCellReadout,
    wholeFirstLiveOverflowPrefix, wholeFirstLiveInclusiveCount, wholeFirstLiveInclusiveCensus,
    wholeFirstLiveInclusiveRecords, wholeFirstLiveOverflowRound, hW, hC, x.property.2,
    firstLiveLength, firstLiveCellReadout, firstLiveOverflowPrefix, firstLiveInclusiveCount,
    firstLiveInclusiveCensus, firstLiveInclusiveRecords, firstLiveOverflowRound]
  exact ⟨trivial, trivial, trivial, trivial, trivial, rfl⟩

/-- No crossing gives the actual empty suffix, rather than a numerical fallback. -/
theorem wholeFirstLive_no_launch (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate source rewards C_star C_h).crossing = none) :
    wholeFirstLiveWindow rate rewards C_star C_h source = [] ∧
    wholeFirstLiveCells rate rewards C_star C_h source = [] ∧
    wholeFirstLiveLength rate rewards C_star C_h source = 0 ∧
    wholeFirstLiveInclusiveCensus rate rewards C_star C_h source = [] ∧
    wholeFirstLiveOverflowRound rate rewards C_star C_h source = none := by
  have hlaunch := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
    rate source rewards C_star C_h).2 hc
  have hW := (ReferenceCompletePhysicalHistory.no_launch_complete_history
    rate source rewards C_star C_h hlaunch).2.1
  have hwindow : wholeFirstLiveWindow rate rewards C_star C_h source = [] := by
    simp only [wholeFirstLiveWindow, hW, ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
      List.takeWhile_nil]
  have hcells : wholeFirstLiveCells rate rewards C_star C_h source = [] := by
    simp only [wholeFirstLiveCells, hc, Option.isSome_none, Bool.false_eq_true, dite_false]
  have hlength : wholeFirstLiveLength rate rewards C_star C_h source = 0 := by
    rw [wholeFirstLiveLength, hwindow, List.length_nil]
  refine ⟨hwindow, hcells, hlength, ?_, ?_⟩
  · simp only [wholeFirstLiveInclusiveCensus, wholeFirstLiveInclusiveRecords,
      hwindow, List.take_nil, List.map_nil]
  · have hpos : 0 < wholeFirstLiveOverflowPrefix rate rewards C_star C_h source :=
      UnstoppedRecordedQueueComparison.first_overflow_prefix_pos _ _
    simp only [wholeFirstLiveOverflowRound, hlength,
      show ¬ wholeFirstLiveOverflowPrefix rate rewards C_star C_h source ≤ 0 from by omega,
      ite_false]

private theorem measurable_on_generated_fibers {Y : Type*} [MeasurableSpace Y]
    (f : BootstrapPrivateRoundStreams.SourceInput p → Y) (empty : Y)
    (hno : ∀ source, (ReferenceCompletePhysicalHistory.generatedBoundary
      rate source rewards C_star C_h).crossing = none → f source = empty)
    (hf : ∀ s : Fin (p.T + 1), Measurable
      (fun x : LaunchFiber rate rewards C_star C_h s.val => f x.val)) : Measurable f := by
  let cover (tag : Option (Fin (p.T + 1))) : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    match tag with
    | none => {source | (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing = none}
    | some s => ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s.val
  have hm (tag) : MeasurableSet (cover tag) := by
    cases tag with
    | none =>
        exact ReferenceCorrectedLaunchMeasurability.measurableSet_generated_no_crossing
          rate rewards C_star C_h
    | some s =>
        exact ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h s.val
  have hc (source) : ∃ tag, source ∈ cover tag := by
    cases h : (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing with
    | none => exact ⟨none, h⟩
    | some crossing =>
        exact ⟨some ⟨ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h,
          Nat.lt_succ_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate source rewards C_star C_h)⟩, by simp only [cover,
              ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet,
              h, Option.isSome_some, true_and, Set.mem_ofPred_eq]⟩
  have hr (tag) : Measurable (fun x : cover tag => f x.val) := by
    cases tag with
    | none => exact measurable_const' (fun x y => (hno x.val x.property).trans (hno y.val y.property).symm)
    | some s => exact hf s
  intro u hu
  have heq : f ⁻¹' u = ⋃ tag, (Subtype.val : cover tag → _) '' {x | f x.val ∈ u} := by
    ext source
    constructor
    · intro hx
      obtain ⟨tag, ht⟩ := hc source
      exact Set.mem_iUnion.mpr ⟨tag, ⟨source, ht⟩, hx, rfl⟩
    · intro hx
      obtain ⟨tag, htag⟩ := Set.mem_iUnion.mp hx
      obtain ⟨x, hxu, hxs⟩ := htag
      rw [← hxs]
      exact hxu
  rw [heq]
  exact MeasurableSet.iUnion (fun tag => MeasurableSet.subtype_image (hm tag) (hr tag hu))

/-- Borel length on the original whole source, including no-launch and terminal strata. -/
theorem measurable_wholeFirstLiveLength :
    Measurable (wholeFirstLiveLength rate rewards C_star C_h) := by
  apply measurable_on_generated_fibers rate rewards C_star C_h _ 0
    (fun source hc => (wholeFirstLive_no_launch rate rewards C_star C_h source hc).2.2.1)
  intro s
  convert measurable_firstLiveLength rate rewards C_star C_h s.val (p.T - s.val) (maximal_span s) using 1
  funext x
  exact (wholeFirstLive_readouts_on_fiber rate rewards C_star C_h s x).1

/-- Original-source Borel numerical readout, with all original private coordinates retained. -/
theorem measurable_wholeFirstLiveCellReadout :
    Measurable (wholeFirstLiveCellReadout rate rewards C_star C_h) := by
  apply measurable_on_generated_fibers rate rewards C_star C_h _ []
  · intro source hc
    rw [wholeFirstLiveCellReadout, (wholeFirstLive_no_launch rate rewards C_star C_h source hc).2.1]
    rfl
  · intro s
    convert measurable_firstLiveCellReadout rate rewards C_star C_h s.val (p.T - s.val) (maximal_span s) using 1
    funext x
    exact (wholeFirstLive_readouts_on_fiber rate rewards C_star C_h s x).2.1

/-- The entire original-source first-live record census is Borel, before the overflow cut. -/
theorem measurable_wholeFirstLiveWindowCensus :
    Measurable (fun source => (wholeFirstLiveWindow rate rewards C_star C_h source).map
      ReferenceActiveHorizonMeasurability.roundRecordCode) := by
  apply measurable_on_generated_fibers rate rewards C_star C_h _ []
  · intro source hc
    rw [(wholeFirstLive_no_launch rate rewards C_star C_h source hc).1]
    rfl
  · intro s
    convert measurable_firstLiveWindowCensus rate rewards C_star C_h s.val (p.T - s.val) (maximal_span s) using 1
    funext x
    rw [(wholeFirstLive_on_fiber rate rewards C_star C_h s x).1]

end OriginalSource

end Bandits.Support.ReferenceFirstLiveOverflowReadout

end
