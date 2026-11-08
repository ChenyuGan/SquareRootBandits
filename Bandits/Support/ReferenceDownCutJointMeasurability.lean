/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceDownReceptionMeasurability

/-!
# Full joint measurability of the existing reference DOWN cut

Sources: `sources/zip4/manuscript/06_interruptions.tex:3-5,192-209,270-276`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,54-60`.
The input state is the original countable carried-state index with its original
real saved-scalar fibers. No validity or physical-history premise is imposed.
The output is exactly the existing lossless reference-cut code; reconstruction
retains the original buffer, including invalid and duplicate records.

The proof uses the accepted ordinary outcome code only on the no-mismatch
branch. A mismatch uses the literal rejection and advanced decoder batch,
before any scan, recovery, or installation. These are internal Borel results,
not manuscript, physical-step, horizon, or regret closure statements.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceDownCutJointMeasurability

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.FollowerDownMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- The original optional view and the ordinary joint row/time/grid/scalar
coordinates, with only the discrete base state fixed. -/
abbrev CutFiberInput (p : Parameters) (rate : RateInput p)
    (state : State p rate.eta) :=
  Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
    FollowerDownJointMeasurability.DownJointInput p state.buffer.length

private abbrev Decoded (p : Parameters) :=
  AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) ×
    Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))

/-- Administrative assembly of the existing code from its measured reads.
This does not define a second cut or evaluate an ordinary operation on a
mismatch branch: `ordinary` is used only when there is no raw mismatch. -/
private def assembleCode (state : State p rate.eta)
    (expected : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (read : FollowerDownJointMeasurability.DownRoundRead p) (valid : Bool) (decoded : Decoded p)
    (ordinary : LocalDownResultCode p rate) : ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate := by
  classical
  exact if read.selected = true ∧ state.status = .unoccupied ∧
      registerInputDomain p rate state ∧ decoderInputDomain p state.downBatch ∧
      valid = true then
    ⟨if decoded.2 = expected then ordinary else
        .decodeOrParseRejected (encodeFollowerState state)
          (encodeFollowerState {state with downBatch := decoded.1}) decoded.2,
      expected, decoded.2, if decoded.2 = expected then decoded.2 else none,
      ReferenceDownReception.ordinaryParse p rate decoded.2,
      decide (ReferenceDownReception.ordinaryLocalAcceptanceTest p rate read.time state
        (ReferenceDownReception.ordinaryParse p rate decoded.2)),
      some (decide (decoded.2 = expected))⟩
  else ⟨ordinary, expected, none, none, none, false, none⟩

private theorem code_ext (a b : ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate)
    (ho : a.outcome = b.outcome) (he : a.expectedWord = b.expectedWord)
    (hr : a.raw = b.raw) (hf : a.filteredRaw = b.filteredRaw)
    (hp : a.ordinaryParse = b.ordinaryParse)
    (ha : a.ordinaryAcceptance = b.ordinaryAcceptance)
    (hc : a.rawComparison = b.rawComparison) : a = b := by
  cases a
  cases b
  cases ho
  cases he
  cases hr
  cases hf
  cases hp
  cases ha
  cases hc
  rfl

private def bufferValidBit (state : State p rate.eta) : Bool := by
  classical
  exact decide (bufferInputDomain p state.buffer)

private instance wordOptionMeasurableSingletonClass (p : Parameters) :
    MeasurableSingletonClass (Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) where
  measurableSet_singleton word := by
    let e := Equiv.optionEquivSumPUnit (AffineChannelLaw.Word (AffineBatchDecoder.width p))
    have he : Measurable e := comap_measurable _
    have hs' : MeasurableSet ({e word} : Set
        (AffineChannelLaw.Word (AffineBatchDecoder.width p) ⊕ PUnit)) := by
      cases hw : e word with
      | inl w =>
          simpa only [Set.image_singleton] using
            (measurableSet_singleton w).inl_image (β := PUnit)
      | inr u =>
          simpa only [Set.image_singleton] using
            (measurableSet_singleton u).inr_image
              (α := AffineChannelLaw.Word (AffineBatchDecoder.width p))
    have hs := he hs'
    have heq : e ⁻¹' {e word} = {word} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact e.injective.eq_iff
    rw [heq] at hs
    exact hs

private theorem adapted_originalScalars (state : State p rate.eta) :
    adaptedInputState rate state
      (FollowerDownJointMeasurability.bufferScalarsCode state.buffer) = state := by
  have hb : replaceBufferScalars state.buffer
      (FollowerDownJointMeasurability.bufferScalarsCode state.buffer) = state.buffer := by
    unfold replaceBufferScalars FollowerDownJointMeasurability.bufferScalarsCode
    calc
      _ = List.ofFn (fun j : Fin state.buffer.length => state.buffer[j.val]) := by
        apply congrArg List.ofFn
        funext j
        cases state.buffer[j]
        rfl
      _ = state.buffer := List.ofFn_getElem
  simp only [adaptedInputState, hb]

/-- The only conditional input is the literal absence of a raw mismatch.
It is discharged by the actual comparison or skipped checks below. -/
private theorem outcomeCode_eq_ordinary
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (k : Fin (D p + 1)) (state : State p rate.eta)
    (hmatch : ¬ ReferenceDownReception.rawMismatch
      (ReferenceDownReception.referenceDownCut p view i row t (feedbackAtGrid p k) rate state)) :
    encodeLocalDownResult
        (ReferenceDownReception.referenceDownCut p view i row t (feedbackAtGrid p k) rate state).outcome =
      encodeLocalDownResult (downTransition p i row t (feedbackAtGrid p k) rate state) := by
  have hstate := adapted_originalScalars (rate := rate) state
  have hm : ¬ ReferenceDownReception.rawMismatch
      (ReferenceDownReception.referenceDownCut p view i row t (feedbackAtGrid p k) rate
        (adaptedInputState rate state
          (FollowerDownJointMeasurability.bufferScalarsCode state.buffer))) := by
    rw [hstate]
    exact hmatch
  have ho := ReferenceDownReceptionMeasurability.referenceDownCut_outcomeCode_eq_downTransitionCode_of_no_raw_mismatch
    view i row t k state (FollowerDownJointMeasurability.bufferScalarsCode state.buffer) hm
  simpa only [FollowerDownJointMeasurability.downTransitionCodeAt, downTransitionCode,
    FollowerDownJointMeasurability.jointRow, FollowerDownJointMeasurability.jointRowTime,
    FollowerDownJointMeasurability.jointTime, FollowerDownJointMeasurability.jointFeedbackIndex,
    FollowerDownJointMeasurability.jointValues, hstate] using ho

private theorem encode_cut_eq_assemble_actual
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (k : Fin (D p + 1)) (state : State p rate.eta) :
    ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode
        (ReferenceDownReception.referenceDownCut p view i row t (feedbackAtGrid p k) rate state) =
      assembleCode state (ReferenceDownReception.expectedDownFlatWord view i row t)
        ⟨t, k, FollowerDownJointMeasurability.downSelectionBit i row t,
          (row.2 t).2 (0, i)⟩
        (bufferValidBit state)
        (currentDecodeStep p i row t (feedbackAtGrid p k) rate state)
        (encodeLocalDownResult (downTransition p i row t (feedbackAtGrid p k) rate state)) := by
  classical
  let cut := ReferenceDownReception.referenceDownCut p view i row t (feedbackAtGrid p k) rate state
  let gate : Prop := downSelected p i row t ∧ state.status = .unoccupied ∧
    registerInputDomain p rate state ∧ decoderInputDomain p state.downBatch ∧
    bufferInputDomain p state.buffer
  have hgate : (FollowerDownJointMeasurability.downSelectionBit i row t = true ∧
      state.status = .unoccupied ∧ registerInputDomain p rate state ∧
      decoderInputDomain p state.downBatch ∧ bufferValidBit state = true)
      ↔ gate := by
    simp only [FollowerDownJointMeasurability.downSelectionBit_eq_true,
      bufferValidBit, decide_eq_true_eq, gate]
  by_cases hg : gate
  · rcases hg with ⟨hs, hstatus, hregisters, hbatch, hbuffer⟩
    have hg' := hgate.mpr ⟨hs, hstatus, hregisters, hbatch, hbuffer⟩
    by_cases hm : (currentDecodeStep p i row t (feedbackAtGrid p k) rate state).2 =
        ReferenceDownReception.expectedDownFlatWord view i row t
    · have hmatch : ¬ ReferenceDownReception.rawMismatch cut := by
        simp only [cut, ReferenceDownReception.rawMismatch, ReferenceDownReception.referenceDownCut,
          hs, hstatus, hregisters, hbatch, hbuffer, hm, ↓reduceDIte,
          Option.some.injEq, Bool.true_eq_false, not_false_eq_true]
      have ho := outcomeCode_eq_ordinary view i row t k state hmatch
      apply code_ext
      · simpa only [ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode,
          assembleCode, ite_eq_left hg', ite_eq_left hm] using ho
      all_goals
        simp only [assembleCode, ite_eq_left hg']
        simp only [ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode,
          ReferenceDownReception.referenceDownCut,
          hs, hstatus, hregisters, hbatch, hbuffer, hm, ↓reduceDIte, ↓reduceIte, decide_true]
    · have hmismatch : ReferenceDownReception.rawMismatch cut := by
        simp only [cut, ReferenceDownReception.rawMismatch, ReferenceDownReception.referenceDownCut,
          hs, hstatus, hregisters, hbatch, hbuffer, hm, ↓reduceDIte]
      have ho := (ReferenceDownReception.referenceDownCut_raw_mismatch_preserves
        view i row t (feedbackAtGrid p k) rate state hs hstatus hregisters hbatch
        hbuffer hmismatch).1
      apply code_ext
      · change encodeLocalDownResult cut.outcome = _
        rw [ho]
        simp only [assembleCode, ite_eq_left hg', ite_eq_right hm, encodeLocalDownResult]
      all_goals
        simp only [assembleCode, ite_eq_left hg']
        simp only [ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode,
          ReferenceDownReception.referenceDownCut,
          hs, hstatus, hregisters, hbatch, hbuffer, hm, ↓reduceDIte, ↓reduceIte, decide_false]
  · have hg' : ¬ (FollowerDownJointMeasurability.downSelectionBit i row t = true ∧
        state.status = .unoccupied ∧ registerInputDomain p rate state ∧
        decoderInputDomain p state.downBatch ∧ bufferValidBit state = true) :=
      fun h => hg (hgate.mp h)
    have hskip : cut.raw = none ∧ cut.filteredRaw = none ∧
        cut.ordinaryParse = none ∧ cut.ordinaryAcceptance = False ∧
        cut.rawComparison = none := by
      dsimp only [cut]
      unfold ReferenceDownReception.referenceDownCut
      dsimp only
      split_ifs <;> simp_all only [gate, not_true_eq_false, and_self, false_and,
        and_false, not_false_eq_true]
    have hmatch : ¬ ReferenceDownReception.rawMismatch cut := by
      simp only [ReferenceDownReception.rawMismatch, hskip.2.2.2.2,
        reduceCtorEq, not_false_eq_true]
    have ho := outcomeCode_eq_ordinary view i row t k state hmatch
    apply code_ext
    · simpa only [ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode,
        assembleCode, ite_eq_right hg'] using ho
    · simpa only [ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode,
        assembleCode, ite_eq_right hg'] using
        ReferenceDownReceptionMeasurability.referenceDownCut_expectedWord_eq
          view i row t (feedbackAtGrid p k) state
    · simpa only [ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode,
        assembleCode, ite_eq_right hg'] using hskip.1
    · simpa only [ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode,
        assembleCode, ite_eq_right hg'] using hskip.2.1
    · simpa only [ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode,
        assembleCode, ite_eq_right hg'] using hskip.2.2.1
    · change decide cut.ordinaryAcceptance = _
      simp only [assembleCode, ite_eq_right hg', hskip.2.2.2.1, decide_false]
    · simpa only [ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode,
        assembleCode, ite_eq_right hg'] using hskip.2.2.2.2

private theorem encode_cut_eq_assemble (i : Fin (p.m - 1))
    (state : State p rate.eta) (x : CutFiberInput p rate state) :
    ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode
        (ReferenceDownReception.referenceDownCut p x.1 i
          (FollowerDownJointMeasurability.jointRow x.2)
          (FollowerDownJointMeasurability.jointTime x.2)
          (feedbackAtGrid p (FollowerDownJointMeasurability.jointFeedbackIndex x.2)) rate
          (adaptedInputState rate state (FollowerDownJointMeasurability.jointValues x.2))) =
      assembleCode state
        (ReferenceDownReception.expectedDownFlatWord x.1 i
          (FollowerDownJointMeasurability.jointRow x.2)
          (FollowerDownJointMeasurability.jointTime x.2))
        (FollowerDownJointMeasurability.downRoundRead i x.2)
        (FollowerDownJointMeasurability.bufferInputValidAt state.buffer
          (FollowerDownJointMeasurability.jointValues x.2))
        (currentDecodeStep p i (FollowerDownJointMeasurability.jointRow x.2)
          (FollowerDownJointMeasurability.jointTime x.2)
          (feedbackAtGrid p (FollowerDownJointMeasurability.jointFeedbackIndex x.2)) rate
          (adaptedInputState rate state (FollowerDownJointMeasurability.jointValues x.2)))
        (FollowerDownJointMeasurability.downTransitionCodeAt i rate state x.2) := by
  classical
  exact encode_cut_eq_assemble_actual x.1 i
    (FollowerDownJointMeasurability.jointRow x.2)
    (FollowerDownJointMeasurability.jointTime x.2)
    (FollowerDownJointMeasurability.jointFeedbackIndex x.2)
    (adaptedInputState rate state (FollowerDownJointMeasurability.jointValues x.2))

/-- Full cut-code measurability while the optional view, entire original row,
time, grid feedback, and original saved scalar family vary jointly. The fixed
base state has no validity premise. -/
theorem measurable_referenceDownCutCode_onFiber (i : Fin (p.m - 1))
    (rate : RateInput p) (state : State p rate.eta) :
    Measurable (fun x : CutFiberInput p rate state =>
      ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode
        (ReferenceDownReception.referenceDownCut p x.1 i
          (FollowerDownJointMeasurability.jointRow x.2)
          (FollowerDownJointMeasurability.jointTime x.2)
          (feedbackAtGrid p (FollowerDownJointMeasurability.jointFeedbackIndex x.2)) rate
          (adaptedInputState rate state (FollowerDownJointMeasurability.jointValues x.2)))) := by
  let reads := fun x : CutFiberInput p rate state =>
    (ReferenceDownReception.expectedDownFlatWord x.1 i
      (FollowerDownJointMeasurability.jointRow x.2)
      (FollowerDownJointMeasurability.jointTime x.2),
      (FollowerDownJointMeasurability.downRoundRead i x.2,
        (FollowerDownJointMeasurability.bufferInputValidAt state.buffer
          (FollowerDownJointMeasurability.jointValues x.2),
          (currentDecodeStep p i (FollowerDownJointMeasurability.jointRow x.2)
            (FollowerDownJointMeasurability.jointTime x.2)
            (feedbackAtGrid p (FollowerDownJointMeasurability.jointFeedbackIndex x.2)) rate
            (adaptedInputState rate state (FollowerDownJointMeasurability.jointValues x.2)),
            FollowerDownJointMeasurability.downTransitionCodeAt i rate state x.2))))
  have he : Measurable (fun x : CutFiberInput p rate state =>
      ReferenceDownReception.expectedDownFlatWord x.1 i
        (FollowerDownJointMeasurability.jointRow x.2)
        (FollowerDownJointMeasurability.jointTime x.2)) :=
    (ReferenceDownReceptionMeasurability.measurable_expectedDownFlatWord i).comp
      (measurable_fst.prodMk ((measurable_fst.comp measurable_fst).comp measurable_snd))
  have hr : Measurable reads := he.prodMk
    (((FollowerDownJointMeasurability.measurable_downRoundRead i state.buffer.length).comp measurable_snd).prodMk
      (((FollowerDownJointMeasurability.measurable_bufferInputValidAt (p := p) state.buffer).comp
        (measurable_snd.comp measurable_snd)).prodMk
        (((ReferenceDownReceptionMeasurability.measurable_currentDecodeStep_joint i rate state).comp measurable_snd).prodMk
          ((FollowerDownJointMeasurability.measurable_downTransitionCode_joint i rate state).comp measurable_snd))))
  have ha : Measurable (fun r :
      Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) ×
        (FollowerDownJointMeasurability.DownRoundRead p ×
          (Bool × (Decoded p × LocalDownResultCode p rate))) => assembleCode state r.1 r.2.1 r.2.2.1
      r.2.2.2.1 r.2.2.2.2) := measurable_of_countable _
  convert ha.comp hr using 1
  funext x
  exact encode_cut_eq_assemble i state x

private theorem measurable_sigmaMk {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (Sigma.mk a : β a → Sigma β) := by
  rw [measurable_iff_le_map]
  change (⨅ i, (inferInstance : MeasurableSpace (β i)).map (Sigma.mk i)) ≤ _
  exact iInf_le _ a

private theorem measurable_of_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro s hs
  change MeasurableSet[
    (⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

/-- Each summand has its original measurable structure, including its images.
No discreteness of the continuous summand is used. -/
private theorem measurableEmbedding_sigmaMk {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] (a : α) :
    MeasurableEmbedding (Sigma.mk a : β a → Sigma β) := by
  classical
  refine ⟨?_, measurable_sigmaMk a, ?_⟩
  · intro x y h
    cases h
    rfl
  · intro s hs
    change MeasurableSet[
      (⨅ b, (inferInstance : MeasurableSpace (β b)).map (Sigma.mk b))]
      (Sigma.mk a '' s)
    rw [MeasurableSpace.measurableSet_iInf]
    intro b
    rw [MeasurableSpace.map_def]
    by_cases h : b = a
    · subst b
      have hinj : Function.Injective (Sigma.mk a : β a → Sigma β) := by
        intro x y hxy
        cases hxy
        rfl
      simpa only [hinj.preimage_image] using hs
    · have hempty : (Sigma.mk b) ⁻¹' (Sigma.mk a '' s) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨y, _, hxy⟩
        exact h (congrArg Sigma.fst hxy).symm
      rw [hempty]
      exact MeasurableSet.empty

/-- Distributing a product into a countable measurable disjoint union is
measurable. Countability is used for the union of the measurable fiber images. -/
private theorem measurable_assembleSigmaProduct {α : Type*} [Countable α]
    {β : α → Type*} [∀ a, MeasurableSpace (β a)]
    {γ : Type*} [MeasurableSpace γ] :
    Measurable (fun x : (Sigma β) × γ =>
      (⟨x.1.1, (x.1.2, x.2)⟩ : Sigma fun a => β a × γ)) := by
  intro s hs
  have hsections (a : α) :
      MeasurableSet ((@Sigma.mk α (fun b => β b × γ) a) ⁻¹' s) := by
    exact (measurable_sigmaMk (β := fun b => β b × γ) a) hs
  have himages (a : α) : MeasurableSet
      ((Prod.map (Sigma.mk a) id) ''
        ((@Sigma.mk α (fun b => β b × γ) a) ⁻¹' s)) :=
    ((measurableEmbedding_sigmaMk a).prodMap MeasurableEmbedding.id).measurableSet_image'
      (hsections a)
  have hdecomp :
      (fun x : (Sigma β) × γ =>
        (⟨x.1.1, (x.1.2, x.2)⟩ : Sigma fun a => β a × γ)) ⁻¹' s =
      ⋃ a : α, (Prod.map (Sigma.mk a) id) ''
        ((@Sigma.mk α (fun b => β b × γ) a) ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨x.1.1, (x.1.2, x.2), hx, rfl⟩
    · intro hx
      obtain ⟨a, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
      subst x
      exact hy
  rw [hdecomp]
  exact MeasurableSet.iUnion himages

/-- The explicit six-coordinate carrier. Its carried state is exactly O's
countable Sigma with the original real saved-scalar family on each fiber. -/
abbrev CutJointInput (p : Parameters) (rate : RateInput p) :=
  Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
    (FollowerObservationStageMeasurabilityRepair.CarriedState p rate ×
      (Fin (p.m - 1) × ((CompleteRow p × Fin p.T) × Fin (D p + 1))))

private theorem measurable_cut_fixedFollower (i : Fin (p.m - 1)) (rate : RateInput p) :
    Measurable (fun x : FollowerObservationStageMeasurabilityRepair.CarriedState p rate ×
        (Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
          ((CompleteRow p × Fin p.T) × Fin (D p + 1))) =>
      ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode
        (ReferenceDownReception.referenceDownCut p x.2.1 i x.2.2.1.1 x.2.2.1.2
          (feedbackAtGrid p x.2.2.2) rate
          (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState x.1.1 x.1.2))) := by
  let f := fun x : Sigma (fun index :
      FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex p rate =>
      SavedScalarFamily index.2.1 ×
        (Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
          ((CompleteRow p × Fin p.T) × Fin (D p + 1)))) =>
    ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode
      (ReferenceDownReception.referenceDownCut p x.2.2.1 i x.2.2.2.1.1 x.2.2.2.1.2
        (feedbackAtGrid p x.2.2.2.2) rate
        (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState x.1 x.2.1))
  have hf : Measurable f := by
    apply measurable_of_sigma_sections
    intro index
    let state := FollowerObservationStageMeasurabilityRepair.representativeState rate index
    have hv : Measurable
        (FollowerObservationStageMeasurabilityRepair.representativeValues index) := by
      apply measurable_pi_iff.mpr
      intro j
      exact measurable_pi_apply
        (Fin.cast (FollowerObservationStageMeasurabilityRepair.sparseSkeletonBuffer_length
          index.2.2) j)
    have hmap : Measurable (fun z : SavedScalarFamily index.2.1 ×
        (Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
          ((CompleteRow p × Fin p.T) × Fin (D p + 1))) =>
        (z.2.1, (z.2.2,
          FollowerObservationStageMeasurabilityRepair.representativeValues index z.1))) :=
      (measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk (hv.comp measurable_fst))
    have hcomp := (measurable_referenceDownCutCode_onFiber i rate state).comp hmap
    convert hcomp using 1
    funext z
    dsimp only [f, Function.comp_def, state,
      FollowerDownJointMeasurability.jointRow, FollowerDownJointMeasurability.jointRowTime,
      FollowerDownJointMeasurability.jointTime, FollowerDownJointMeasurability.jointFeedbackIndex,
      FollowerDownJointMeasurability.jointValues]
    rw [FollowerObservationStageMeasurabilityRepair.adaptedRepresentativeState_eq_reconstruct]
  exact hf.comp measurable_assembleSigmaProduct

/-- Unconditional joint Borel measurability of the FULL existing lossless
reference DOWN cut code, including the varying original carried state and
follower. All raw/filtered/parse/acceptance/comparison diagnostics and every
ordinary outcome constructor are present. -/
theorem measurable_referenceDownCutCode_joint (p : Parameters) (rate : RateInput p) :
    Measurable (fun x : CutJointInput p rate =>
      ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode
        (ReferenceDownReception.referenceDownCut p x.1 x.2.2.1
          x.2.2.2.1.1 x.2.2.2.1.2 (feedbackAtGrid p x.2.2.2.2) rate
          (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
            x.2.1.1 x.2.1.2))) := by
  have hf : Measurable (fun x :
      (FollowerObservationStageMeasurabilityRepair.CarriedState p rate ×
        (Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
          ((CompleteRow p × Fin p.T) × Fin (D p + 1)))) × Fin (p.m - 1) =>
      ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode
        (ReferenceDownReception.referenceDownCut p x.1.2.1 x.2
          x.1.2.2.1.1 x.1.2.2.1.2 (feedbackAtGrid p x.1.2.2.2) rate
          (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
            x.1.1.1 x.1.1.2))) :=
    measurable_from_prod_countable_left fun i => measurable_cut_fixedFollower i rate
  have hmap : Measurable (fun x : CutJointInput p rate =>
      ((x.2.1, (x.1, x.2.2.2)), x.2.2.1)) :=
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  exact hf.comp hmap

/-- Composition from SIX separately measurable coordinate maps. There is no
assumption that a dependent assembled input or the target operation is measurable. -/
theorem measurable_referenceDownCutCode_comp {Ω : Type*} [MeasurableSpace Ω]
    (rate : RateInput p)
    (view : Ω → Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (carry : Ω → FollowerObservationStageMeasurabilityRepair.CarriedState p rate)
    (i : Ω → Fin (p.m - 1)) (row : Ω → CompleteRow p) (t : Ω → Fin p.T)
    (feedbackIndex : Ω → Fin (D p + 1))
    (hview : Measurable view) (hcarry : Measurable carry) (hi : Measurable i)
    (hrow : Measurable row) (ht : Measurable t) (hfeedback : Measurable feedbackIndex) :
    Measurable (fun ω =>
      ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode
        (ReferenceDownReception.referenceDownCut p (view ω) (i ω) (row ω) (t ω)
          (feedbackAtGrid p (feedbackIndex ω)) rate
          (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
            (carry ω).1 (carry ω).2))) :=
  (measurable_referenceDownCutCode_joint p rate).comp
    (hview.prodMk (hcarry.prodMk (hi.prodMk ((hrow.prodMk ht).prodMk hfeedback))))

/-- Exact lossless reconstruction on this representation, using M's accepted
unconditional theorem and the ENTIRE original carried buffer. -/
theorem referenceDownCutCode_reconstruct
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (carry : FollowerObservationStageMeasurabilityRepair.CarriedState p rate)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (feedbackIndex : Fin (D p + 1)) :
    ReferenceDownReceptionMeasurability.reconstructReferenceDownCutCode
        (ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode
          (ReferenceDownReception.referenceDownCut p view i row t
            (feedbackAtGrid p feedbackIndex) rate
            (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState carry.1 carry.2)))
        (FollowerObservationStageMeasurabilityRepair.carriedStateBuffer carry) =
      ReferenceDownReception.referenceDownCut p view i row t
        (feedbackAtGrid p feedbackIndex) rate
        (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState carry.1 carry.2) :=
  ReferenceDownReceptionMeasurability.reconstruct_encode_referenceDownCut
    view i row t (feedbackAtGrid p feedbackIndex) _

end Bandits.Support.ReferenceDownCutJointMeasurability

end
