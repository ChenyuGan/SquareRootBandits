/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAuxiliarySeeds

/-!
# An analytical renewal draw at the actual first collection call

Sources: `sources/zip4/manuscript/06_interruptions.tex:52-55,376-426`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:176-215`, and
`sources/zip4/manuscript/07_public_setup.tex:121-164`.

The source subtype retains the whole physical source, including every row,
private array and the original private index. Its measure is unnormalized.
Renewal is tested against the incoming ledger in the existing lossless suffix
code. The selected parameter is obtained from the actual present call.

All weights in this file are reconstructed stored weights. Identifying them
with the manuscript score process, providing the chronological logical path,
and coupling a current physical assignment vector remain separate obligations.
The extra scalar array is analytical and changes no physical transition.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw

open ConstructorDimensions

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev Rewards := ActualInitializationPhysicalStep.GridRewardTable
abbrev Scalar := ContinuousControlSlice.Scalar
abbrev AuxiliaryArray := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
abbrev AuxiliaryCellIndex {p : Parameters} (u t : Fin p.T) :=
  ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t
abbrev Theta := AssignmentParameterFibreKernel.Theta
abbrev SlowSet (p : Parameters) := CanonicalOrientedSetLaw.SlowSet p.K p.m
abbrev RecordCode (p : Parameters) (rate : RateInput p) :=
  ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)

variable {p : Parameters}

local instance optionNatMeasurableSpace : MeasurableSpace (Option ℕ) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance optionNatDiscrete : DiscreteMeasurableSpace (Option ℕ) := by
  constructor
  intro s
  let e := Equiv.optionEquivSumPUnit ℕ
  exact ⟨e '' s, measurableSet_sum_iff.mpr
    ⟨MeasurableSet.of_discrete, MeasurableSet.of_discrete⟩, e.injective.preimage_image s⟩

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩
local instance outcomeMeasurableSpace : MeasurableSpace (Option (SlowSet p)) := ⊤
local instance outcomeDiscrete : DiscreteMeasurableSpace (Option (SlowSet p)) :=
  ⟨fun _ => trivial⟩

/-- Only the original incoming collection tag has an old freeze boundary. -/
def coordinatorFreezeAt? (rate : RateInput p) :
    ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate → Option ℕ
  | .inr (.inr (.inl (_, ledger, _))) => some ledger.freezeAt
  | _ => none

theorem measurable_coordinatorFreezeAt? (rate : RateInput p) :
    Measurable (coordinatorFreezeAt? rate) := by
  apply measurable_fun_sum measurable_const
  apply measurable_fun_sum measurable_const
  apply measurable_fun_sum _ measurable_const
  exact (measurable_of_countable (fun ledger : ReferenceActivePhysicalStep.Ledger rate =>
    some ledger.freezeAt)).comp (measurable_fst.comp measurable_snd)

/-- Search the existing lossless suffix for the actual timestamp, then read
the incoming collection ledger. No replacement snapshot or default is used. -/
def oldFreezeAt? (rate : RateInput p) (rewards : Rewards p) (C_star C_h : ℝ)
    (t : Fin p.T) (source : SourceInput p) : Option ℕ :=
  ((ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
    (rate := rate) rewards C_star C_h source).find? (fun code => code.1 = t.val)).bind
      (fun code => coordinatorFreezeAt? rate code.2.1.1)

private theorem listObservationCoordinates_injective {A : Type*} :
    Function.Injective (ReferenceActiveHorizonMeasurability.listObservationCoordinates
      (α := A)) := by
  intro l r h
  apply List.ext_getElem?
  intro n
  have hn := congrFun (congrArg Prod.snd h) n
  change ReferenceActiveHorizonMeasurability.listObservationAt l n =
    ReferenceActiveHorizonMeasurability.listObservationAt r n at hn
  unfold ReferenceActiveHorizonMeasurability.listObservationAt at hn
  cases hl : l[n]? <;> cases hr : r[n]? <;> simp_all

-- This countable readout contains only timestamps and optional natural
-- boundaries. The original continuous record space keeps its Borel structure.
private instance discreteCalendarTagSingletons :
    MeasurableSingletonClass (Unit ⊕ (ℕ × Option ℕ)) := by
  constructor
  intro value
  cases value with
  | inl x =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton x).inl_image (β := ℕ × Option ℕ)
  | inr x =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton x).inr_image (α := Unit)

private instance discreteCalendarSingletons :
    MeasurableSingletonClass (List (ℕ × Option ℕ)) := by
  constructor
  intro l
  have heq : ({l} : Set (List (ℕ × Option ℕ))) =
      ReferenceActiveHorizonMeasurability.listObservationCoordinates ⁻¹'
        {ReferenceActiveHorizonMeasurability.listObservationCoordinates l} := by
    ext r
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h ▸ rfl, fun h => listObservationCoordinates_injective h⟩
  rw [heq]
  exact ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
    (measurableSet_singleton _)

/-- The optional old boundary is Borel without discretizing any real field. -/
theorem measurable_oldFreezeAt? (rate : RateInput p) (rewards : Rewards p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (oldFreezeAt? rate rewards C_star C_h t) := by
  let readout : RecordCode p rate → ℕ × Option ℕ :=
    fun code => (code.1, coordinatorFreezeAt? rate code.2.1.1)
  have hreadout : Measurable readout :=
    measurable_fst.prodMk ((measurable_coordinatorFreezeAt? rate).comp
      (measurable_fst.comp (measurable_fst.comp measurable_snd)))
  have hcalendar := ReferenceActiveHorizonMeasurability.measurable_list_map
    (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
      (rate := rate) rewards C_star C_h)
    (ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
      (rate := rate) rewards C_star C_h) readout hreadout
  have hsearch : Measurable (fun l : List (ℕ × Option ℕ) =>
      (l.find? (fun cell => cell.1 = t.val)).bind Prod.snd) :=
    measurable_of_countable _
  convert hsearch.comp hcalendar using 1
  funext source
  simp only [Function.comp_apply, List.find?_map, Option.bind_map, readout, oldFreezeAt?]

private theorem find?_of_nodup_map {A B : Type*} [DecidableEq B]
    (f : A → B) (l : List A) (a : A) (ha : a ∈ l) (hn : (l.map f).Nodup) :
    l.find? (fun b => f b = f a) = some a := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      simp only [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.mp ha with hab | ha
      · subst a
        simp
      · have hne : f b ≠ f a := by
          intro h
          exact hn.1 (h ▸ List.mem_map.mpr ⟨a, ha, rfl⟩)
        simpa [hne] using ih ha hn.2

/-- On an actual record the timestamp search reads precisely its incoming
ledger. The complete suffix has distinct physical timestamps. -/
theorem oldFreezeAt?_eq_of_record (rate : RateInput p) (rewards : Rewards p)
    (C_star C_h : ℝ) (t : Fin p.T) (source : SourceInput p)
    (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
    (hr : r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)
    (htime : r.input.time = t)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hcoord : r.input.state.coordinator = .collection payload ledger saved) :
    oldFreezeAt? rate rewards C_star C_h t source = some ledger.freezeAt := by
  let code := ReferenceActiveHorizonMeasurability.roundRecordCode r
  let codes := ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
    (rate := rate) rewards C_star C_h source
  have hmem : code ∈ codes := List.mem_map.mpr ⟨r, hr, rfl⟩
  have hn : (codes.map Prod.fst).Nodup := by
    rw [ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode_times]
    exact List.nodup_range'
  have hfind := find?_of_nodup_map Prod.fst codes code hmem hn
  have hcodeTime : code.1 = t.val := congrArg Fin.val htime
  change (codes.find? (fun c => c.1 = t.val)).bind _ = _
  rw [← hcodeTime, hfind]
  simp only [Option.bind_some, code, ReferenceActiveHorizonMeasurability.roundRecordCode,
    ReferenceActivePhysicalStepMeasurability.encodeState, hcoord,
    ReferenceActivePhysicalStepMeasurability.encodeCoordinator, coordinatorFreezeAt?]

/-- The literal actual-call cell with the incoming old boundary reached. -/
def renewalCallEvent (rate : RateInput p) (rewards : Rewards p) (C_star C_h : ℝ)
    (u t : Fin p.T) : Set (SourceInput p) :=
  {source | source ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t ∧
    ∃ g, oldFreezeAt? rate rewards C_star C_h t source = some g ∧ g ≤ t.val + 1}

theorem measurableSet_renewalCallEvent (rate : RateInput p) (rewards : Rewards p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    MeasurableSet (renewalCallEvent rate rewards C_star C_h u t) := by
  apply (ReferenceFirstCollectionAuxiliarySeeds.measurableSet_actualCollectionCallCell
    rate rewards C_star C_h u t).inter
  change MeasurableSet {source | ∃ g, _}
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro g
  exact (measurableSet_eq_fun (measurable_oldFreezeAt? rate rewards C_star C_h t)
    measurable_const).inter (MeasurableSet.const _)

/-- Whole physical sources on a renewal cell; no positive-mass condition. -/
abbrev RenewalCallSource (rate : RateInput p) (rewards : Rewards p) (C_star C_h : ℝ)
    (u t : Fin p.T) := ↥(renewalCallEvent rate rewards C_star C_h u t)

/-- The finite, unnormalized pullback of the original physical law. -/
def renewalSourceLaw (rate : RateInput p) (rewards : Rewards p) (C_star C_h : ℝ)
    (u t : Fin p.T) : Measure (RenewalCallSource rate rewards C_star C_h u t) :=
  (BootstrapPrivateRoundStreams.sourceInputLaw p).comap Subtype.val

instance renewalSourceLaw_finite (rate : RateInput p) (rewards : Rewards p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    IsFiniteMeasure (renewalSourceLaw rate rewards C_star C_h u t) := by
  constructor
  rw [renewalSourceLaw, comap_subtype_coe_apply
    (measurableSet_renewalCallEvent rate rewards C_star C_h u t)]
  exact measure_lt_top _ _

/-- The subtype law pushes forward to restriction of the original source
law, with its original mass and all original coordinates retained. -/
theorem renewalSourceLaw_map_val (rate : RateInput p) (rewards : Rewards p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    (renewalSourceLaw rate rewards C_star C_h u t).map Subtype.val =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (renewalCallEvent rate rewards C_star C_h u t) :=
  map_comap_subtype_coe (measurableSet_renewalCallEvent rate rewards C_star C_h u t) _

/-- In particular this is the source event mass, rather than a normalized
conditional probability. A null actual cell has zero total mass. -/
theorem renewalSourceLaw_univ (rate : RateInput p) (rewards : Rewards p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    renewalSourceLaw rate rewards C_star C_h u t Set.univ =
      BootstrapPrivateRoundStreams.sourceInputLaw p
        (renewalCallEvent rate rewards C_star C_h u t) := by
  rw [renewalSourceLaw, comap_subtype_coe_apply
    (measurableSet_renewalCallEvent rate rewards C_star C_h u t)]
  rw [Set.image_univ, Subtype.range_coe]

variable (rate : RateInput p) (rewards : Rewards p) (C_star C_h : ℝ) (u t : Fin p.T)

theorem renewalCall_isSome (z : RenewalCallSource rate rewards C_star C_h u t) :
    (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z.val).isSome := by
  have h := z.property.1
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
    rate rewards C_star C_h z.val).map _ = some (u, t) at h
  cases hc : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z.val with
  | none => simp [hc] at h
  | some call => rfl

/-- Actual present-call extraction by `Option.get`, with no fallback. -/
def renewalCallParameter (z : RenewalCallSource rate rewards C_star C_h u t) : Theta p :=
  ((ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z.val).get
    (renewalCall_isSome rate rewards C_star C_h u t z)).2.2

theorem firstCollectionCall_eq (z : RenewalCallSource rate rewards C_star C_h u t) :
    ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z.val =
      some (u, (t, renewalCallParameter rate rewards C_star C_h u t z)) := by
  have h := z.property.1
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
    rate rewards C_star C_h z.val).map _ = some (u, t) at h
  let c := (ReferenceFirstCollectionSamplerCall.firstCollectionCall
    rate rewards C_star C_h z.val).get (renewalCall_isSome rate rewards C_star C_h u t z)
  have hc : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z.val = some c := (Option.some_get _).symm
  rw [hc] at h
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
  rw [hc]
  exact congrArg some (Prod.ext h.1 (Prod.ext h.2 rfl))

private theorem measurableSet_some_image {A : Type*} [MeasurableSpace A]
    (s : Set A) (hs : MeasurableSet s) : MeasurableSet (some '' s : Set (Option A)) := by
  change MeasurableSet[(inferInstance : MeasurableSpace (A ⊕ PUnit)).comap
    (Equiv.optionEquivSumPUnit A)] (some '' s)
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Sum.inl '' s, measurableSet_inl_image.mpr hs, ?_⟩
  ext value
  cases value <;> simp

theorem measurable_renewalCallParameter :
    Measurable (renewalCallParameter rate rewards C_star C_h u t) := by
  intro s hs
  have hcall : Measurable (fun z : RenewalCallSource rate rewards C_star C_h u t =>
      ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z.val) :=
    (ReferenceFirstCollectionSamplerCall.measurable_firstCollectionCall
    rate rewards C_star C_h).comp measurable_subtype_coe
  have hset := measurableSet_some_image
    {c : ReferenceFirstCollectionSamplerCall.Call p | c.2.2 ∈ s}
    ((measurable_snd.comp measurable_snd) hs)
  convert hcall hset using 1
  ext z
  simp only [Set.mem_preimage]
  rw [firstCollectionCall_eq rate rewards C_star C_h u t z]
  simp

/-- The physical collection input formed from the original input and ledger. -/
abbrev collectionView (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (old : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool)) :=
  ReferenceActivePhysicalStep.collectionInput x old ledger
    (ReferenceActivePhysicalStep.collectionClock old ledger saved u) u

/-- Produced witnesses of the actual clock/core/reconstruction call. These
are observations of an existing record, rather than a new protocol state. -/
structure ActualRenewalCall (z : RenewalCallSource rate rewards C_star C_h u t) where
  record : ReferenceFirstCollectionSamplerCall.RoundRecord p rate
  record_mem : record ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z.val rewards C_star C_h
  time_eq : record.input.time = t
  old : ReferenceActivePhysicalStep.Payload rate
  ledger : ReferenceActivePhysicalStep.Ledger rate
  saved : Option (Fin p.T × Bool)
  coordinator_eq : record.input.state.coordinator = .collection old ledger saved
  cutoff_eq : ledger.cutoff = u.val + 1
  freeze_le : ledger.freezeAt ≤ t.val + 1
  started : CoordinatorPhaseClock.StartRoundResult p
  clock_eq : CoordinatorPhaseClock.startRound p rate.eta.val record.input.time
    (ReferenceActivePhysicalStep.collectionClock old ledger saved u) ledger.pending = .ok started
  core : CoordinatorRoundDispatch.CollectionCoreValid (collectionView rate u record.input old ledger saved)
  instruction : CoordinatorPhaseClock.AssignmentStartInstruction p
  instruction_eq : started.assignmentStart = some instruction
  instruction_time : instruction.time = record.input.time
  renewal : instruction.kind = .renewal
  out : AssignmentScoreReconstruction.ReconstructedStart
    (CoordinatorRoundDispatch.collectionOperationLedger
      (collectionView rate u record.input old ledger saved) core.payload_n_eq) instruction
  reconstruction_eq : AssignmentScoreReconstruction.reconstructLaterStart
    (CoordinatorRoundDispatch.collectionOperationLedger
      (collectionView rate u record.input old ledger saved) core.payload_n_eq) instruction =
      .success _ instruction out
  parameter_eq : renewalCallParameter rate rewards C_star C_h u t z =
    LaterAssignmentStartMeasurability.selectedSamplerParameters old
      (CoordinatorRoundDispatch.collectionOperationLedger
        (collectionView rate u record.input old ledger saved) core.payload_n_eq)
      instruction out reconstruction_eq

/-- No clock, kind, reconstruction, positivity or physical sampling success
is assumed: all witnesses come from the actual present prechoice selector. -/
theorem actual_renewal_call_parameters (z : RenewalCallSource rate rewards C_star C_h u t) :
    Nonempty (ActualRenewalCall rate rewards C_star C_h u t z) := by
  classical
  obtain ⟨n, r, hr, htime, hcall, _⟩ :=
    (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec rewards C_star C_h z.val u t
      (renewalCallParameter rate rewards C_star C_h u t z)).mp
      (firstCollectionCall_eq rate rewards C_star C_h u t z)
  obtain ⟨old, ledger, saved, hcoord, hcut, hparameter⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u
      (renewalCallParameter rate rewards C_star C_h u t z)).mp hcall
  have hmem := List.mem_of_getElem? hr
  have hfreezeRead := oldFreezeAt?_eq_of_record rate rewards C_star C_h t z.val
    r hmem htime old ledger saved hcoord
  obtain ⟨g, hg, hgle⟩ := z.property.2
  rw [hfreezeRead] at hg
  have hfreeze : ledger.freezeAt ≤ t.val + 1 := Option.some.inj hg ▸ hgle
  have hcutValid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    have hu := u.isLt
    omega
  have hcutIndex : (⟨ledger.cutoff - 1, by omega⟩ : Fin p.T) = u := by
    apply Fin.ext
    dsimp
    omega
  change ReferenceLaterAssignmentFibreStep.parameters? r.input = some _ at hparameter
  simp only [ReferenceLaterAssignmentFibreStep.parameters?, hcoord,
    dite_eq_left hcutValid, hcutIndex] at hparameter
  let x := collectionView rate u r.input old ledger saved
  change ReferenceLaterAssignmentFibreStep.collectionParameters? x = some _ at hparameter
  unfold ReferenceLaterAssignmentFibreStep.collectionParameters? at hparameter
  cases hclock : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock x.ledger.pending with
  | error reason => simp [hclock] at hparameter
  | ok started =>
      simp only [hclock] at hparameter
      by_cases core : CoordinatorRoundDispatch.CollectionCoreValid x
      · rw [dite_eq_left core] at hparameter
        by_cases hpending : x.ledger.pending.Nonempty
        · simp [hpending] at hparameter
        · rw [ite_eq_right hpending] at hparameter
          cases hinstruction : started.assignmentStart with
          | none => simp [hinstruction] at hparameter
          | some instruction =>
              simp only [hinstruction] at hparameter
              rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match]
                at hparameter
              cases hd : LaterAssignmentStartOperation.decideReconstruction x.payload
                  (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
                  instruction with
              | failure reason => simp [hd] at hparameter
              | success out hrec =>
                  rw [hd] at hparameter
                  have htheta := (Option.some.inj hparameter).symm
                  have hitime := (CoordinatorPhaseClock.startRound_assignment_effect p
                    x.etaReal x.time x.clock x.ledger.pending started instruction
                    core.clock_parameter_valid core.clock_registers_valid
                    core.clock_start_time_valid hclock hinstruction).1
                  have hrenewal : instruction.kind = .renewal :=
                    (AssignmentScoreReconstruction.reconstructLaterStart_renewal_iff
                      _ instruction out hrec).mpr (by
                        change ledger.freezeAt ≤ instruction.time.val + 1
                        rw [hitime]
                        change ledger.freezeAt ≤ r.input.time.val + 1
                        simpa only [htime] using hfreeze)
                  exact ⟨{
                    record := r
                    record_mem := hmem
                    time_eq := htime
                    old := old
                    ledger := ledger
                    saved := saved
                    coordinator_eq := hcoord
                    cutoff_eq := hcut
                    freeze_le := hfreeze
                    started := started
                    clock_eq := hclock
                    core := core
                    instruction := instruction
                    instruction_eq := hinstruction
                    instruction_time := hitime
                    renewal := hrenewal
                    out := out
                    reconstruction_eq := hrec
                    parameter_eq := htheta }⟩
      · simp [core] at hparameter

/-- The actual core forces the physical cutoff to precede this call time. -/
theorem renewalCall_cutoff_le_time (z : RenewalCallSource rate rewards C_star C_h u t) :
    u.val ≤ t.val := by
  obtain ⟨d⟩ := actual_renewal_call_parameters rate rewards C_star C_h u t z
  have h := d.core.clock_start_time_valid
  change CoordinatorPhaseClock.startRoundTimeValid p d.record.input.time
    (ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u) at h
  simpa only [CoordinatorPhaseClock.startRoundTimeValid,
    ReferenceActivePhysicalStep.collectionClock, d.time_eq] using h.2

/-- Positivity and the product-weight parameter are consequences of the
successful reconstruction and the reached old boundary. -/
theorem renewal_parameter_spec (z : RenewalCallSource rate rewards C_star C_h u t) :
    (∀ a, 0 < (renewalCallParameter rate rewards C_star C_h u t z).2 a) ∧
    (renewalCallParameter rate rewards C_star C_h u t z).1 =
      LaterAssignmentStartOperation.productQOnPrefixCarrier
        (renewalCallParameter rate rewards C_star C_h u t z).2 := by
  obtain ⟨d⟩ := actual_renewal_call_parameters rate rewards C_star C_h u t z
  obtain ⟨ha, hm⟩ := LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
    d.old _ d.instruction d.out d.reconstruction_eq d.renewal
  rw [d.parameter_eq]
  constructor
  · rw [ha]
    exact (LaterAssignmentStartMeasurability.successfulLawSelection
      d.old _ d.instruction d.out d.reconstruction_eq).currentWeightPos
  · rw [ha]
    exact funext hm

/-- Stored score meaning is explicit; no manuscript score truth is asserted. -/
theorem actual_renewal_stored_score (z : RenewalCallSource rate rewards C_star C_h u t)
    (d : ActualRenewalCall rate rewards C_star C_h u t z) (a : Fin p.K) :
    AssignmentScoreReconstruction.sourceScore d.out a =
      (d.out.registers.cutoff a).score + d.ledger.increment a := rfl

/-- An unconditional source-subtype producer of the actual reconstructed
weight equality and the literal stored score formula. The output witness is
the original call evidence, not an assumed physical score trajectory. -/
theorem actual_renewal_call_weight_equations
    (z : RenewalCallSource rate rewards C_star C_h u t) :
    ∃ d : ActualRenewalCall rate rewards C_star C_h u t z,
      (renewalCallParameter rate rewards C_star C_h u t z).2 =
          AssignmentScoreReconstruction.currentWeight d.out ∧
      (∀ a, 0 < AssignmentScoreReconstruction.currentWeight d.out a) ∧
      (∀ a, AssignmentScoreReconstruction.sourceScore d.out a =
        (d.out.registers.cutoff a).score + d.ledger.increment a) := by
  obtain ⟨d⟩ := actual_renewal_call_parameters rate rewards C_star C_h u t z
  have heq := (LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
    d.old _ d.instruction d.out d.reconstruction_eq d.renewal).1
  refine ⟨d, ?_, ?_, fun a => actual_renewal_stored_score rate rewards C_star C_h u t z d a⟩
  · rw [d.parameter_eq]
    exact heq
  · exact (LaterAssignmentStartMeasurability.successfulLawSelection
      d.old _ d.instruction d.out d.reconstruction_eq).currentWeightPos

/-- The canonical slow-set PMF with both current and anchor weights equal to
the actual selected renewal weight. -/
def renewalSlowSetPMF (z : RenewalCallSource rate rewards C_star C_h u t) :
    PMF (SlowSet p) :=
  CanonicalOrientedSetLaw.slowSetPMF
    (renewalCallParameter rate rewards C_star C_h u t z).2
    (renewalCallParameter rate rewards C_star C_h u t z).2 p.two_le_m p.m_lt_K
    (renewal_parameter_spec rate rewards C_star C_h u t z).1
    (renewal_parameter_spec rate rewards C_star C_h u t z).1

/-- Every supported slow set has positive mass under the produced weights. -/
theorem renewalSlowSetPMF_pos (z : RenewalCallSource rate rewards C_star C_h u t)
    (U : SlowSet p) : 0 < renewalSlowSetPMF rate rewards C_star C_h u t z U :=
  CanonicalOrientedSetLaw.slowSetPMF_apply_pos _ _ p.two_le_m p.m_lt_K
    (renewal_parameter_spec rate rewards C_star C_h u t z).1
    (renewal_parameter_spec rate rewards C_star C_h u t z).1 U

/-- Identification with the existing full-vector fibre mass, for every
supported slow set, with all local positivity conditions discharged. -/
theorem renewal_parameter_fibreMass (z : RenewalCallSource rate rewards C_star C_h u t)
    (U : SlowSet p) :
    AssignmentParameterFibreKernel.fibreMass p
        (renewalCallParameter rate rewards C_star C_h u t z) (some U) =
      renewalSlowSetPMF rate rewards C_star C_h u t z U ∧
    AssignmentParameterFibreKernel.fibreMass p
        (renewalCallParameter rate rewards C_star C_h u t z) none = 0 := by
  let w := (renewalCallParameter rate rewards C_star C_h u t z).2
  have hw : ∀ a, 0 < w a := (renewal_parameter_spec rate rewards C_star C_h u t z).1
  have htheta : renewalCallParameter rate rewards C_star C_h u t z =
      ((CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K w hw).weight,
        w) := by
    refine Prod.ext ?_ rfl
    exact (renewal_parameter_spec rate rewards C_star C_h u t z).2
  have hsample (v : CheckedAssignmentSample.AssignmentVector p) :
      AssignmentParameterFibreKernel.successfulSlowSet p
        (renewalCallParameter rate rewards C_star C_h u t z) v =
      some (CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
        w w hw hw v) := by
    rw [htheta]
    unfold AssignmentParameterFibreKernel.successfulSlowSet
    rw [CheckedAssignmentSample.productQ_checkedAssignmentSample_eq_sampler p w w hw hw]
    rfl
  constructor
  · change ContinuousControlSlice.assignmentLaw p.K {v | _ = some U} = _
    simp_rw [hsample, Option.some.injEq]
    change FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
      (CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K w w hw hw) U = _
    rw [CanonicalAssignmentVector.canonicalSlowSampler_fibreMass,
      renewalSlowSetPMF, CanonicalOrientedSetLaw.slowSetPMF_apply]
  · change ContinuousControlSlice.assignmentLaw p.K {v | _ = none} = 0
    simp_rw [hsample]
    simp

/-- Joint Borel mass dependence comes from the existing varying-parameter
full-vector fibre theorem, specialized to the produced renewal parameter. -/
theorem measurable_renewalSlowSetPMF (U : SlowSet p) :
    Measurable (fun z : RenewalCallSource rate rewards C_star C_h u t =>
      renewalSlowSetPMF rate rewards C_star C_h u t z U) := by
  have hm := (AssignmentParameterFibreKernel.measurable_fibreMass_joint p).comp
    ((measurable_renewalCallParameter rate rewards C_star C_h u t).prodMk
      (measurable_const (a := some U)))
  convert hm using 1
  funext z
  exact (renewal_parameter_fibreMass rate rewards C_star C_h u t z U).1.symm

/-- A fixed enumeration of the existing finite supported slow-set carrier. -/
def slowSetEnumeration (p : Parameters) : Fin (Fintype.card (SlowSet p)) ≃ SlowSet p :=
  (Fintype.equivFin (SlowSet p)).symm

theorem slowSet_card_pos (p : Parameters) : 0 < Fintype.card (SlowSet p) := by
  have hpmf := CanonicalOrientedSetLaw.slowSetPMF (fun _ : Fin p.K => (1 : ℝ))
    (fun _ => 1) p.two_le_m p.m_lt_K (by intro a; norm_num) (by intro a; norm_num)
  obtain ⟨U, _⟩ := hpmf.support_nonempty
  exact Fintype.card_pos_iff.mpr ⟨U⟩

/-- Literal real PMF atoms in this one fixed enumeration. -/
def renewalAtomMass (z : RenewalCallSource rate rewards C_star C_h u t)
    (i : Fin (Fintype.card (SlowSet p))) : ℝ :=
  (renewalSlowSetPMF rate rewards C_star C_h u t z (slowSetEnumeration p i)).toReal

theorem renewalAtomMass_nonneg (z : RenewalCallSource rate rewards C_star C_h u t)
    (i : Fin (Fintype.card (SlowSet p))) :
    0 ≤ renewalAtomMass rate rewards C_star C_h u t z i := ENNReal.toReal_nonneg

theorem renewalAtomMass_sum (z : RenewalCallSource rate rewards C_star C_h u t) :
    ∑ i, renewalAtomMass rate rewards C_star C_h u t z i = 1 := by
  classical
  simp only [renewalAtomMass]
  rw [(slowSetEnumeration p).sum_comp (fun U =>
    (renewalSlowSetPMF rate rewards C_star C_h u t z U).toReal)]
  rw [← ENNReal.toReal_sum (fun U _ => (renewalSlowSetPMF rate rewards C_star C_h u t z).apply_ne_top U)]
  have hsum : ∑ U, renewalSlowSetPMF rate rewards C_star C_h u t z U = 1 := by
    simpa only [tsum_fintype] using (renewalSlowSetPMF rate rewards C_star C_h u t z).tsum_coe
  rw [hsum, ENNReal.toReal_one]

theorem measurable_renewalAtomMass (i : Fin (Fintype.card (SlowSet p))) :
    Measurable (fun z : RenewalCallSource rate rewards C_star C_h u t =>
      renewalAtomMass rate rewards C_star C_h u t z i) :=
  (measurable_renewalSlowSetPMF rate rewards C_star C_h u t
    (slowSetEnumeration p i)).ennreal_toReal

/-- One categorical draw from the actual reconstructed renewal PMF. The
input scalar is separate analytical randomness, never a physical fallback. -/
def renewalScalarSample (z : RenewalCallSource rate rewards C_star C_h u t)
    (v : Scalar) : SlowSet p :=
  slowSetEnumeration p (ContinuousCategorical.sample (slowSet_card_pos p)
    (renewalAtomMass rate rewards C_star C_h u t z)
    (renewalAtomMass_sum rate rewards C_star C_h u t z) v)

/-- The requested analytical sampler uses exactly label 1 at time `t`. -/
def renewalAuxiliarySample (z : RenewalCallSource rate rewards C_star C_h u t)
    (a : AuxiliaryArray p) : SlowSet p :=
  renewalScalarSample rate rewards C_star C_h u t z (a (t, 1))

/-- Exact half-open cumulative fibre, now with its source-varying masses. -/
theorem renewalScalarSample_eq_iff (z : RenewalCallSource rate rewards C_star C_h u t)
    (v : Scalar) (U : SlowSet p) :
    renewalScalarSample rate rewards C_star C_h u t z v = U ↔
      ContinuousCategorical.lower (renewalAtomMass rate rewards C_star C_h u t z)
        ((slowSetEnumeration p).symm U) ≤ v.val ∧
      v.val < ContinuousCategorical.upper (renewalAtomMass rate rewards C_star C_h u t z)
        ((slowSetEnumeration p).symm U) := by
  unfold renewalScalarSample
  rw [← Equiv.eq_symm_apply]
  exact ContinuousCategorical.sample_eq_iff (slowSet_card_pos p)
    (renewalAtomMass_nonneg rate rewards C_star C_h u t z)
    (renewalAtomMass_sum rate rewards C_star C_h u t z) v _

/-- Every cumulative sum is jointly Borel in the physical source. -/
theorem measurable_renewalLower (i : Fin (Fintype.card (SlowSet p))) :
    Measurable (fun z : RenewalCallSource rate rewards C_star C_h u t =>
      ContinuousCategorical.lower (renewalAtomMass rate rewards C_star C_h u t z) i) := by
  classical
  unfold ContinuousCategorical.lower
  exact Finset.measurable_sum _ (fun j _ =>
    measurable_renewalAtomMass rate rewards C_star C_h u t j)

theorem measurable_renewalUpper (i : Fin (Fintype.card (SlowSet p))) :
    Measurable (fun z : RenewalCallSource rate rewards C_star C_h u t =>
      ContinuousCategorical.upper (renewalAtomMass rate rewards C_star C_h u t z) i) := by
  classical
  unfold ContinuousCategorical.upper
  exact Finset.measurable_sum _ (fun j _ =>
    measurable_renewalAtomMass rate rewards C_star C_h u t j)

/-- This proves joint fibres with varying source parameters, rather than
merely fixed-mass measurability of a scalar sampler. -/
theorem measurable_renewalScalarSample :
    Measurable (fun w : RenewalCallSource rate rewards C_star C_h u t × Scalar =>
      renewalScalarSample rate rewards C_star C_h u t w.1 w.2) := by
  apply measurable_to_countable'
  intro U
  have heq : (fun w : RenewalCallSource rate rewards C_star C_h u t × Scalar =>
      renewalScalarSample rate rewards C_star C_h u t w.1 w.2) ⁻¹' {U} =
      {w | ContinuousCategorical.lower (renewalAtomMass rate rewards C_star C_h u t w.1)
          ((slowSetEnumeration p).symm U) ≤ w.2.val ∧
        w.2.val < ContinuousCategorical.upper (renewalAtomMass rate rewards C_star C_h u t w.1)
          ((slowSetEnumeration p).symm U)} := by
    ext w
    exact renewalScalarSample_eq_iff rate rewards C_star C_h u t w.1 w.2 U
  rw [heq]
  have hv : Measurable (fun w : RenewalCallSource rate rewards C_star C_h u t × Scalar =>
      w.2.val) := measurable_subtype_coe.comp measurable_snd
  exact (measurableSet_le ((measurable_renewalLower rate rewards C_star C_h u t _).comp
      measurable_fst) hv).inter
    (measurableSet_lt hv ((measurable_renewalUpper rate rewards C_star C_h u t _).comp
      measurable_fst))

theorem measurable_renewalAuxiliarySample :
    Measurable (fun w : RenewalCallSource rate rewards C_star C_h u t × AuxiliaryArray p =>
      renewalAuxiliarySample rate rewards C_star C_h u t w.1 w.2) := by
  apply measurable_to_countable'
  intro U
  have hv : Measurable (fun w : RenewalCallSource rate rewards C_star C_h u t ×
      AuxiliaryArray p => (w.2 (t, 1)).val) :=
    measurable_subtype_coe.comp ((measurable_pi_apply (t, 1)).comp measurable_snd)
  have hset := (measurableSet_le
      ((measurable_renewalLower rate rewards C_star C_h u t
        ((slowSetEnumeration p).symm U)).comp measurable_fst) hv).inter
    (measurableSet_lt hv
      ((measurable_renewalUpper rate rewards C_star C_h u t
        ((slowSetEnumeration p).symm U)).comp measurable_fst))
  convert hset using 1
  ext w
  exact renewalScalarSample_eq_iff rate rewards C_star C_h u t w.1 (w.2 (t, 1)) U

/-- Uniform lengths of the categorical fibres are precisely the PMF atoms. -/
theorem renewalScalarSample_fibre (z : RenewalCallSource rate rewards C_star C_h u t)
    (U : SlowSet p) :
    ContinuousControlSlice.scalarLaw
      {v | renewalScalarSample rate rewards C_star C_h u t z v = U} =
        renewalSlowSetPMF rate rewards C_star C_h u t z U := by
  have heq : {v | renewalScalarSample rate rewards C_star C_h u t z v = U} =
      ContinuousCategorical.sample (slowSet_card_pos p)
        (renewalAtomMass rate rewards C_star C_h u t z)
        (renewalAtomMass_sum rate rewards C_star C_h u t z) ⁻¹'
          {(slowSetEnumeration p).symm U} := by
    ext v
    exact (slowSetEnumeration p).eq_symm_apply.symm
  rw [heq]
  change ContinuousCategorical.uniform _ = _
  rw [ContinuousCategorical.uniform_sample_singleton (slowSet_card_pos p)
    (renewalAtomMass_nonneg rate rewards C_star C_h u t z)
    (renewalAtomMass_sum rate rewards C_star C_h u t z), renewalAtomMass,
    Equiv.apply_symm_apply, ENNReal.ofReal_toReal
      ((renewalSlowSetPMF rate rewards C_star C_h u t z).apply_ne_top U)]

/-- The renewal coordinate is outside the old trigger/collection block.
This conditional finite-index helper is consumed with actual chronology. -/
theorem renewal_coordinate_not_mem (hut : u.val ≤ t.val) :
    ¬ ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellIndexPredicate u t (t, 1) := by
  simp only [ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellIndexPredicate]
  omega

/-- Actual chronology supplies the finite-index helper's only condition. -/
theorem actual_renewal_coordinate_not_mem
    (z : RenewalCallSource rate rewards C_star C_h u t) :
    ¬ ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellIndexPredicate u t (t, 1) :=
  renewal_coordinate_not_mem u t (renewalCall_cutoff_le_time rate rewards C_star C_h u t z)

/-- The old block and the single new renewal scalar have their joint product
law. Its explicit chronology premise is produced on every nonempty actual cell. -/
theorem auxiliaryBlock_renewalScalar_measurePreserving (hut : u.val ≤ t.val) :
    MeasurePreserving
      (fun a : AuxiliaryArray p =>
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryBlock u t a, a (t, 1)))
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
      ((ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t).prod
        ContinuousControlSlice.scalarLaw) := by
  classical
  let pred := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellIndexPredicate u t
  let Complement := {q : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p // ¬ pred q}
  let q : Complement := ⟨(t, 1), renewal_coordinate_not_mem u t hut⟩
  let split := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p => Scalar) pred
  have hsplit : MeasurePreserving split
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
      ((ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t).prod
        (Measure.pi (fun _ : Complement => ContinuousControlSlice.scalarLaw))) := by
    exact measurePreserving_piEquivPiSubtypeProd
      (fun _ : ReferenceFirstCollectionAuxiliarySeeds.Coordinate p =>
        ContinuousControlSlice.scalarLaw) pred
  have heval := measurePreserving_eval
    (fun _ : Complement => ContinuousControlSlice.scalarLaw) q
  have hid : MeasurePreserving (id : (AuxiliaryCellIndex u t → Scalar) → _)
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t)
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t) := MeasurePreserving.id _
  exact (hid.prod heval).comp hsplit

/-- Keep the entire source and old auxiliary block, exposing only the extra
renewal scalar as the last independent factor. -/
def renewalCoordinateSplit
    (w : RenewalCallSource rate rewards C_star C_h u t × AuxiliaryArray p) :
    (RenewalCallSource rate rewards C_star C_h u t × (AuxiliaryCellIndex u t → Scalar)) ×
      Scalar :=
  ((w.1, ReferenceFirstCollectionAuxiliarySeeds.auxiliaryBlock u t w.2), w.2 (t, 1))

theorem renewalCoordinateSplit_measurePreserving (hut : u.val ≤ t.val) :
    MeasurePreserving (renewalCoordinateSplit rate rewards C_star C_h u t)
      ((renewalSourceLaw rate rewards C_star C_h u t).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p))
      (((renewalSourceLaw rate rewards C_star C_h u t).prod
        (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t)).prod
          ContinuousControlSlice.scalarLaw) := by
  have hid := MeasurePreserving.id (renewalSourceLaw rate rewards C_star C_h u t)
  have hprod := hid.prod (auxiliaryBlock_renewalScalar_measurePreserving u t hut)
  have hassoc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (renewalSourceLaw rate rewards C_star C_h u t)
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t)
      ContinuousControlSlice.scalarLaw)
  exact hassoc.comp hprod

/-- Source-indexed, unnormalized joint fibre identity. The test may depend
jointly on the whole source and every old block coordinate. Null cells are
included, and the right side is an ENNReal restricted nonnegative integral. -/
theorem renewalAuxiliarySample_joint_fibre
    (Aset : Set (RenewalCallSource rate rewards C_star C_h u t ×
      (AuxiliaryCellIndex u t → Scalar))) (hA : MeasurableSet Aset) (U : SlowSet p) :
    ((renewalSourceLaw rate rewards C_star C_h u t).prod
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p))
      {w | (w.1, ReferenceFirstCollectionAuxiliarySeeds.auxiliaryBlock u t w.2) ∈ Aset ∧
        renewalAuxiliarySample rate rewards C_star C_h u t w.1 w.2 = U} =
      ∫⁻ x in Aset, renewalSlowSetPMF rate rewards C_star C_h u t x.1 U
        ∂(renewalSourceLaw rate rewards C_star C_h u t).prod
          (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t) := by
  classical
  by_cases hz : Nonempty (RenewalCallSource rate rewards C_star C_h u t)
  · obtain ⟨z⟩ := hz
    have hsplit := renewalCoordinateSplit_measurePreserving rate rewards C_star C_h u t
      (renewalCall_cutoff_le_time rate rewards C_star C_h u t z)
    let Bset : Set ((RenewalCallSource rate rewards C_star C_h u t ×
        (AuxiliaryCellIndex u t → Scalar)) × Scalar) :=
      {w | w.1 ∈ Aset ∧ renewalScalarSample rate rewards C_star C_h u t w.1.1 w.2 = U}
    have hB : MeasurableSet Bset := by
      exact (measurable_fst hA).inter
        (((measurable_renewalScalarSample rate rewards C_star C_h u t).comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
            (measurableSet_singleton U))
    calc
      _ = (((renewalSourceLaw rate rewards C_star C_h u t).prod
          (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t)).prod
            ContinuousControlSlice.scalarLaw) Bset := by
        rw [← hsplit.map_eq, Measure.map_apply hsplit.measurable hB]
        rfl
      _ = ∫⁻ x, ContinuousControlSlice.scalarLaw (Prod.mk x ⁻¹' Bset)
          ∂(renewalSourceLaw rate rewards C_star C_h u t).prod
            (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t) :=
        Measure.prod_apply hB
      _ = ∫⁻ x, Aset.indicator
          (fun x => renewalSlowSetPMF rate rewards C_star C_h u t x.1 U) x
          ∂(renewalSourceLaw rate rewards C_star C_h u t).prod
            (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryCellLaw u t) := by
        apply lintegral_congr
        intro x
        by_cases hx : x ∈ Aset
        · simp only [Bset, Set.preimage_ofPred_eq, hx, true_and, Set.indicator_of_mem hx]
          exact renewalScalarSample_fibre rate rewards C_star C_h u t x.1 U
        · have hempty : Prod.mk x ⁻¹' Bset = ∅ := by
            ext v
            simp [Bset, hx]
          simp only [hempty, measure_empty, Set.indicator_of_notMem hx]
      _ = _ := lintegral_indicator hA _
  · let : IsEmpty (RenewalCallSource rate rewards C_star C_h u t) :=
      not_nonempty_iff.mp hz
    have hzero : renewalSourceLaw rate rewards C_star C_h u t = 0 := Subsingleton.elim _ _
    simp only [hzero, Measure.zero_prod, Measure.coe_zero, Pi.zero_apply, Measure.restrict_zero,
      lintegral_zero_measure]

/-- The actual selected parameter has a finite unnormalized parameter law. -/
def renewalParameterLaw : Measure (Theta p) :=
  (renewalSourceLaw rate rewards C_star C_h u t).map
    (renewalCallParameter rate rewards C_star C_h u t)

instance renewalParameterLaw_finite :
    IsFiniteMeasure (renewalParameterLaw rate rewards C_star C_h u t) := by
  unfold renewalParameterLaw
  infer_instance

/-- Named downstream kernel consumer at the actual parameter and analytical
sample. This does not identify any current physical assignment vector. -/
def renewalAssignmentFibreKernel : ProbabilityTheory.Kernel
    (RenewalCallSource rate rewards C_star C_h u t × AuxiliaryArray p)
    (CheckedAssignmentSample.AssignmentVector p) :=
  (AssignmentParameterFibreKernel.assignmentParameterFibreKernel p).comap
    (fun w => (renewalCallParameter rate rewards C_star C_h u t w.1,
      some (renewalAuxiliarySample rate rewards C_star C_h u t w.1 w.2)))
    (((measurable_renewalCallParameter rate rewards C_star C_h u t).comp
      measurable_fst).prodMk
        ((measurable_of_countable (some : SlowSet p → Option (SlowSet p))).comp
          (measurable_renewalAuxiliarySample rate rewards C_star C_h u t)))

theorem renewalAssignmentFibreKernel_apply
    (z : RenewalCallSource rate rewards C_star C_h u t) (a : AuxiliaryArray p) :
    renewalAssignmentFibreKernel rate rewards C_star C_h u t (z, a) =
      AssignmentParameterFibreKernel.assignmentParameterFibreKernel p
        (renewalCallParameter rate rewards C_star C_h u t z,
          some (renewalAuxiliarySample rate rewards C_star C_h u t z a)) := rfl

/-- The named kernel consumer always receives a positive supported fibre;
the checked failure outcome has mass zero by `renewal_parameter_fibreMass`. -/
theorem renewal_sample_fibreMass_pos
    (z : RenewalCallSource rate rewards C_star C_h u t) (a : AuxiliaryArray p) :
    0 < AssignmentParameterFibreKernel.fibreMass p
      (renewalCallParameter rate rewards C_star C_h u t z)
      (some (renewalAuxiliarySample rate rewards C_star C_h u t z a)) := by
  rw [(renewal_parameter_fibreMass rate rewards C_star C_h u t z _).1]
  exact renewalSlowSetPMF_pos rate rewards C_star C_h u t z _

/-- The existing finite-parameter kernel identity is available at this actual
parameter law. It reconstructs the abstract full-vector law, not a coupling
to a claimed physical current vector or a conditional-history process. -/
theorem renewalParameterLaw_jointMeasure_eq_map :
    AssignmentParameterFibreKernel.jointMeasure p
        (renewalParameterLaw rate rewards C_star C_h u t) =
      ((renewalParameterLaw rate rewards C_star C_h u t).prod
        (ContinuousControlSlice.assignmentLaw p.K)).map
        (fun w => ((w.1, AssignmentParameterFibreKernel.successfulSlowSet p w.1 w.2), w.2)) :=
  AssignmentParameterFibreKernel.jointMeasure_eq_map p _

end Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw

end
