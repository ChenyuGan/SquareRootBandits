/-
Copyright (c) 2026 Bandits Lean formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAssignmentNonRead
public import Bandits.Support.ReferenceFirstCollectionAuxiliarySeeds

import Mathlib.Tactic

/-!
# Retained first-collection observation and independent auxiliary block

Sources: `sources/zip4/manuscript/06_interruptions.tex:38-100,376-408`,
`04_slow_fast_learner.tex:176-188`, and `appendix_b_communication.tex:25-58`.

The observation below consists solely of projections of the original physical
source. It includes optional numerical slots and stopped queue readouts at
all boundaries through `T`. It neither replaces the physical execution nor
identifies a physical filtration. Its deterministic assignment non-read law
and the independent analytical auxiliary-block product law are separate facts.
The latter is unnormalized and applies even to nonmeasurable restricting sets.
Neither fact is an adaptive resampling law or a logical deferred-refresh law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionDeferredCalendarProduct

open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable selectedRowIndex)
open ReferenceActivePhysicalStep (RateInput)
open ReferenceCompletePhysicalHistory (physicalStart completeSuffixRecords)
open ReferenceFirstLiveConfirmationHistory (firstLiveWindow)
open ReferenceFirstCollectionSamplerCall (firstCollectionCall)
open ReferenceFirstCollectionPrecallCalendarSupport
  (firstCallBoundary cutBoundary precallSlots precallCells? precallReadout?)
open ReferenceFirstCollectionCurrentRetainedGate (cell0)
open ReferenceCoordinatorRecorderCallTrace (cell)
open ReferenceActiveHorizonMeasurability (roundRecordCode)
open ReferenceLaterCollectionSourceReadoutMeasurability
  (numericalCoordinates arrivalCoordinates arrivalsFromNumerical)
open ReferenceFirstLaunchNumericalCell (queueParameters)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open RecordedQueueRun (RoundInput run)

local instance optionMeasurableSpace {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Option α) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "S" => SourceInput p
local notation "R" z:max => completeSuffixRecords rate z rewards C_star C_h
local notation "s" z:max => physicalStart rate z rewards C_star C_h
local notation "b" z:max => firstCallBoundary rate rewards C_star C_h z

/-- The end of the first original LIVE window, in calendar coordinates. -/
def assignmentBegin (z : S) : ℕ := s z + (firstLiveWindow (R z)).length

/-- The original call cells strictly before invocation, with absent calls
and absent recorder outputs retained as distinct options. -/
def precallTrace (z : S) :=
  ((R z).take (b z - s z)).map (cell ∘ roundRecordCode)

/-- The literal gate/arrival diagnostics on the same strict prefix. -/
def precallRaw (z : S) : List (Option (Fin p.K × ℕ)) :=
  ((R z).take (b z - s z)).map ReferenceCollectionRawBufferHistory.rawDiagnostic

/-- The complete optional numerical coordinates of every dated prefix slot. -/
def slotObservation (n : ℕ) (z : S) :=
  (precallSlots rate rewards C_star C_h n z).map (Option.map numericalCoordinates)

/-- The incoming-state mask is only an observation cut. It creates no state
at an absent input or beyond the original first-call boundary. -/
def incomingObservation (t : Fin p.T) (z : S) :=
  if t.val ≤ b z then
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z
  else none

abbrev NumericalCoordinates (p : Parameters) :=
  Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ)))

abbrev QueueReadout (p : Parameters) :=
  (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))

/-- Ordinary existing product, option, list and finite-function carriers.
The real reward and rate vectors retain their Borel structures. -/
abbrev Observation (p : Parameters) (rate : RateInput p) :=
  Fin (M p) × (ℕ × (ℕ × (Option (ReferenceFirstCollectionSamplerCall.Call p) ×
    (List (Option (ReferenceCompleteNumericalBranchObservation.TraceCellData rate)) ×
      (List (Option (Fin p.K × ℕ)) ×
        ((Fin (p.T + 1) → List (Option (NumericalCoordinates p))) ×
          ((Fin (p.T + 1) → Option (QueueReadout p)) ×
            (Fin p.T → Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate)))))))))

/-- The measurable structure is the ordinary product of the existing
constituent spaces, cached here to avoid deep product instance searches. -/
instance observationMeasurableSpace : MeasurableSpace (Observation p rate) :=
  MeasurableSpace.prod inferInstance
    (MeasurableSpace.prod inferInstance
      (MeasurableSpace.prod inferInstance
        (MeasurableSpace.prod inferInstance
          (MeasurableSpace.prod inferInstance
            (MeasurableSpace.prod inferInstance
              (MeasurableSpace.prod inferInstance
                (MeasurableSpace.prod inferInstance inferInstance)))))))

/-- One retained observation of the actual first collection. A failed first
invocation is a call; no call keeps its existing terminal-boundary convention.
`none` and `some []` are never identified. -/
def observation (z : S) : Observation p rate :=
  (selectedRowIndex p z, s z, assignmentBegin rate rewards C_star C_h z,
    firstCollectionCall rate rewards C_star C_h z,
    precallTrace rate rewards C_star C_h z, precallRaw rate rewards C_star C_h z,
    (fun n => slotObservation rate rewards C_star C_h n.val z),
    (fun n => precallReadout? rate rewards C_star C_h n.val z),
    (fun t => incomingObservation rate rewards C_star C_h t z))

private theorem measurable_option_map {Y A B : Type*}
    [MeasurableSpace Y] [MeasurableSpace A] [MeasurableSpace B]
    (f : Y → Option A) (hf : Measurable f) (g : A → B) (hg : Measurable g) :
    Measurable (fun y => (f y).map g) :=
  ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun q : A × Y => g q.1) (hg.comp measurable_fst) f hf

private instance sumMeasurableSingleton {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
    | inr value => simpa only [Set.image_singleton] using (MeasurableSet.singleton value).inr_image

private instance optionMeasurableSingleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Option α) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit α))
      (MeasurableSet.singleton (Equiv.optionEquivSumPUnit α x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage, (Equiv.optionEquivSumPUnit α).injective.eq_iff]

private instance listMeasurableSingleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (List α) where
  measurableSet_singleton L := by
    have hinj : Function.Injective
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := α)) := by
      intro A B h
      have hlen : A.length = B.length := congrArg Prod.fst h
      apply List.ext_getElem hlen
      intro k hk hk'
      have he := congrFun (congrArg Prod.snd h) k
      simpa only [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
        ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Sum.inr.injEq] using he
    have hh := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (MeasurableSet.singleton
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates L))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

private theorem measurable_list_take {Y α : Type*} [MeasurableSpace Y] [MeasurableSpace α]
    (records : Y → List α) (hrecords : Measurable records)
    (n : Y → ℕ) (hn : Measurable n) :
    Measurable (fun x => (records x).take (n x)) := by
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
    by_cases hj : j < n x <;> simp only [hj, ite_true, ite_false]
  apply measurable_comap_iff.mpr
  convert hlen.prodMk ht using 1
  funext x
  exact Prod.ext List.length_take rfl

private theorem measurable_selectedRow : Measurable (selectedRowIndex p) :=
  BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p

/-- The actual endpoint retains the horizon sentinel on the absent branch. -/
theorem measurable_firstCallBoundary :
    Measurable (firstCallBoundary rate rewards C_star C_h) := by
  have htime := measurable_option_map
    (firstCollectionCall rate rewards C_star C_h)
    (ReferenceFirstCollectionSamplerCall.measurable_firstCollectionCall
      rate rewards C_star C_h)
    (fun c : ReferenceFirstCollectionSamplerCall.Call p => c.2.1.val)
    ((measurable_of_countable Fin.val).comp (measurable_fst.comp measurable_snd))
  convert (measurable_of_countable (fun n : Option ℕ => n.getD p.T)).comp htime using 1
  funext z
  cases h : firstCollectionCall rate rewards C_star C_h z <;>
    simp only [firstCallBoundary, h, Option.map_none, Option.getD_none,
      Option.map_some, Option.getD_some, Function.comp_apply]

/-- Original physical start plus the original first LIVE length is Borel. -/
theorem measurable_assignmentBegin :
    Measurable (assignmentBegin rate rewards C_star C_h) := by
  exact (measurable_of_countable (fun v : ℕ × ℕ => v.1 + v.2)).comp
    ((ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).prodMk
      (ReferenceFirstLiveOverflowReadout.measurable_wholeFirstLiveLength
        rate rewards C_star C_h))

private theorem measurable_prefixLength :
    Measurable (fun z : S => b z - s z) :=
  (measurable_of_countable (fun v : ℕ × ℕ => v.1 - v.2)).comp
    ((measurable_firstCallBoundary rate rewards C_star C_h).prodMk
      (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
        rate rewards C_star C_h))

/-- The lossless codes are cut before applying their existing cell projection. -/
theorem measurable_precallTrace :
    Measurable (precallTrace rate rewards C_star C_h) := by
  have hprefix := measurable_list_take _
    (ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
      (rate := rate) rewards C_star C_h) _
    (measurable_prefixLength rate rewards C_star C_h)
  have hmap := ReferenceActiveHorizonMeasurability.measurable_list_map _ hprefix _
    (ReferenceCoordinatorRecorderCallTrace.measurable_cell (p := p) (rate := rate))
  change Measurable (fun z : S => ((R z).take (b z - s z)).map (cell ∘ roundRecordCode))
  convert hmap using 1
  funext z
  simp only [ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
    List.map_take, List.map_map]

private def rawFromCode
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :
    Option (Fin p.K × ℕ) :=
  (ReferenceCoordinatorRecorderCallTrace.recording code).bind fun output =>
    output.gateArm.map fun arm => (arm, output.rawArrival)

private theorem measurable_rawFromCode : Measurable (rawFromCode (p := p) (rate := rate)) := by
  have hrecording : Measurable
      (ReferenceCoordinatorRecorderCallTrace.recording (p := p) (rate := rate)) := by
    unfold ReferenceCoordinatorRecorderCallTrace.recording
      ReferenceCoordinatorRecorderCallTrace.tail
    fun_prop
  exact (measurable_of_countable (fun output : Option (CoordinatorRecordingOperation.Output p) =>
    output.bind fun out => out.gateArm.map fun arm => (arm, out.rawArrival))).comp hrecording

private theorem rawFromCode_actual
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    rawFromCode rate (roundRecordCode r) = ReferenceCollectionRawBufferHistory.rawDiagnostic r := by
  unfold rawFromCode ReferenceCollectionRawBufferHistory.rawDiagnostic
  rw [ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics]
  rfl

/-- Actual raw diagnostics are Borel through the existing record-code bridge. -/
theorem measurable_precallRaw : Measurable (precallRaw rate rewards C_star C_h) := by
  have hprefix := measurable_list_take _
    (ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
      (rate := rate) rewards C_star C_h) _
    (measurable_prefixLength rate rewards C_star C_h)
  have hmap := ReferenceActiveHorizonMeasurability.measurable_list_map _ hprefix _
    (measurable_rawFromCode (p := p) (rate := rate))
  convert hmap using 1
  funext z
  simp only [precallRaw, ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
    List.map_take, List.map_map, Function.comp_def, rawFromCode_actual]

/-- The coordinate bridge uses the public branch projections, rather than
placing any measurable structure on raw evidence or certified queue inputs. -/
private theorem cell0_coordinates
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    (cell0 rate r).map ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates =
      (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r).map
        (Sum.elim id id) := by
  have hp := ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 r
  rw [cell0, Option.map_or]
  have hl := congrArg Prod.fst hp
  have hr := congrArg Prod.snd hp
  change ReferenceCompleteNumericalBranchObservation.leftProjection _ =
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).map
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates at hl
  change ReferenceCompleteNumericalBranchObservation.rightProjection _ =
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates at hr
  rw [← hl, ← hr]
  cases h : ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r with
  | none => rfl
  | some value => cases value <;> rfl

private theorem slotObservation_eq_take (n : ℕ) (z : S) :
    slotObservation rate rewards C_star C_h n z =
      ((ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h z).take
          (cutBoundary rate rewards C_star C_h n z - s z)).map
        (fun e => e.2.2.map (Sum.elim id id)) := by
  have hn : cutBoundary rate rewards C_star C_h n z - s z ≤ (R z).length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    apply Nat.sub_le_sub_right
    exact (Nat.min_le_right _ _).trans
      (ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_le_T
        rate rewards C_star C_h z)
  simp only [ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
    ReferenceCompleteNumericalBranchObservation.branchCalendar, List.map_take, List.map_map,
    Function.comp_def]
  apply List.ext_getElem
  · simp only [slotObservation, precallSlots, List.length_map, List.length_range,
      List.length_take, Nat.min_eq_left hn]
  · intro k hk hk'
    have hkn : k < cutBoundary rate rewards C_star C_h n z - s z := by
      simpa only [slotObservation, precallSlots, List.length_map, List.length_range] using hk
    have hkR : k < (R z).length := lt_of_lt_of_le hkn hn
    simp only [slotObservation, precallSlots, List.getElem_map, List.getElem_range,
      List.getElem_take]
    rw [List.getElem?_eq_getElem hkR, Option.bind_some]
    exact cell0_coordinates rate _

/-- Whole-source measurability of the literal optional numerical slots at
any natural boundary. In particular `n = T` is included directly. -/
theorem measurable_slotObservation (n : ℕ) :
    Measurable (slotObservation rate rewards C_star C_h n) := by
  have hcut : Measurable (fun z : S => cutBoundary rate rewards C_star C_h n z - s z) :=
    (measurable_of_countable (fun v : ℕ × ℕ => min n v.1 - v.2)).comp
      ((measurable_firstCallBoundary rate rewards C_star C_h).prodMk
        (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
          rate rewards C_star C_h))
  have hprefix := measurable_list_take _
    (ReferenceCompleteNumericalBranchObservation.measurable_completeBranchObservation
      rate rewards C_star C_h) _ hcut
  have hentry : Measurable
      (fun e : ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        e.2.2.map (Sum.elim id id)) :=
    measurable_option_map _ (measurable_snd.comp measurable_snd) _
      (measurable_id.sumElim measurable_id)
  have hmap := ReferenceActiveHorizonMeasurability.measurable_list_map _ hprefix _ hentry
  convert hmap using 1
  funext z
  exact slotObservation_eq_take rate rewards C_star C_h n z

private theorem measurable_of_countable_fibers {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Countable A] [MeasurableSpace B] (g : X → A) (hg : Measurable g)
    (f : X → B) (hf : ∀ x y, g x = g y → f x = f y) : Measurable f := by
  intro U _
  have he : f ⁻¹' U = ⋃ v ∈ g '' (f ⁻¹' U), g ⁻¹' {v} := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨g x, Set.mem_iUnion.mpr
        ⟨⟨x, hx, rfl⟩, rfl⟩⟩
    · intro hx
      obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hx
      obtain ⟨⟨y, hy, hgy⟩, hxv⟩ := Set.mem_iUnion.mp hv
      have heq := hf x y (hxv.trans hgy.symm)
      change f x ∈ U
      rw [heq]
      exact hy
  rw [he]
  exact MeasurableSet.iUnion (fun v => MeasurableSet.iUnion (fun _ =>
    (MeasurableSet.singleton v).preimage hg))

private theorem step_eq_of_arrivalCoordinates
    (state : RecordedQueueRun.RunState p.K) (c d : RoundInput p.K)
    (h : ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate c =
      ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate d) :
    RecordedQueueRun.step (queueParameters rate) state c =
      RecordedQueueRun.step (queueParameters rate) state d := by
  have he : c.enabled = d.enabled := congrArg Prod.fst h
  have ha (j : Fin p.K) : RecordedQueueRun.quantizedArrival (queueParameters rate) c j =
      RecordedQueueRun.quantizedArrival (queueParameters rate) d j :=
    congrFun (congrArg Prod.snd h) j
  simp only [RecordedQueueRun.step, RecordedQueueRun.acceptedRecord, he, ha]
  rfl

private theorem execute_eq_of_arrivalCoordinates
    (L M : List (RoundInput p.K))
    (h : L.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate) =
      M.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate))
    (state : RecordedQueueRun.RunState p.K) :
    RecordedQueueRun.execute (queueParameters rate) L state =
      RecordedQueueRun.execute (queueParameters rate) M state := by
  induction L generalizing M state with
  | nil =>
      cases M with
      | nil => rfl
      | cons c M => simp at h
  | cons c L ih =>
      cases M with
      | nil => simp at h
      | cons d M =>
          simp only [List.map_cons, List.cons.injEq] at h
          simp only [RecordedQueueRun.execute]
          rw [step_eq_of_arrivalCoordinates rate state c d h.1]
          exact ih M h.2 _

private theorem mapM_map_coordinates {A B : Type*}
    (slots : List (Option A)) (f : A → B) :
    (slots.mapM id).map (List.map f) =
      (slots.map (Option.map f)).mapM id := by
  induction slots with
  | nil => rfl
  | cons c slots ih =>
      cases c with
      | none => simp [List.mapM_cons]
      | some c =>
          cases ht : slots.mapM id with
          | none => simp [List.mapM_cons, ← ih, ht]
          | some L => simp [List.mapM_cons, ← ih, ht]

private theorem optional_run_congr (L M : List (Option (RoundInput p.K)))
    (h : L.map (Option.map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate)) =
      M.map (Option.map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate))) :
    (L.mapM id).map (fun cells => stateReadout (run (queueParameters rate) cells)) =
      (M.mapM id).map (fun cells => stateReadout (run (queueParameters rate) cells)) := by
  have he := congrArg (fun slots => slots.mapM id) h
  rw [← mapM_map_coordinates, ← mapM_map_coordinates] at he
  cases hL : L.mapM id with
  | none =>
      cases hM : M.mapM id with
      | none => rfl
      | some cells => simp only [hL, hM, Option.map_none, Option.map_some, reduceCtorEq] at he
  | some cells =>
      cases hM : M.mapM id with
      | none => simp only [hL, hM, Option.map_none, Option.map_some, reduceCtorEq] at he
      | some other =>
          simp only [hL, hM, Option.map_some, Option.some.injEq] at he
          have hrun := execute_eq_of_arrivalCoordinates rate cells other he
            (RecordedQueueRun.initialState p.K)
          exact congrArg (fun state => some (stateReadout state)) hrun

private theorem measurableSet_launchAtCut (n : ℕ) : MeasurableSet
    {z : S | ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h (cutBoundary rate rewards C_star C_h n z) z} := by
  have he : {z : S | ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h (cutBoundary rate rewards C_star C_h n z) z} =
      ⋃ j : ℕ, ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h j ∩
        {z | j ≤ cutBoundary rate rewards C_star C_h n z} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet,
      ReferenceSourcePrefixHistoryFiltration.actualLaunchBy]
    constructor
    · rintro ⟨hc, hs⟩
      exact ⟨s z, ⟨hc, rfl⟩, hs⟩
    · rintro ⟨j, ⟨hc, hj⟩, hs⟩
      exact ⟨hc, hj ▸ hs⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro j
  exact (ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
    (rate := rate) rewards C_star C_h j).inter
    (measurableSet_le measurable_const
      ((measurable_of_countable (fun k : ℕ => min n k)).comp
        (measurable_firstCallBoundary rate rewards C_star C_h)))

/-- The existing stopped numerical run is Borel at every natural boundary,
including the terminal one. This proof retains the detecting overflow update
and distinguishes absent prefixes from present empty prefixes. -/
theorem measurable_precallReadout (n : ℕ) :
    Measurable (precallReadout? rate rewards C_star C_h n) := by
  have hmap : Measurable (fun c : Option (NumericalCoordinates p) =>
      c.map (arrivalsFromNumerical rate)) :=
    measurable_option_map id measurable_id _
      (ReferenceLaterCollectionSourceReadoutMeasurability.measurable_arrivalsFromNumerical rate)
  have harrivals : Measurable (fun z : S =>
      (precallSlots rate rewards C_star C_h n z).map (Option.map (arrivalCoordinates rate))) := by
    have h := ReferenceActiveHorizonMeasurability.measurable_list_map _
      (measurable_slotObservation rate rewards C_star C_h n) _ hmap
    simpa only [slotObservation, List.map_map, Option.map_map, Function.comp_def,
      ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical_numericalCoordinates]
      using h
  let g := fun z : S =>
    if ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
        (cutBoundary rate rewards C_star C_h n z) z then
      some ((precallSlots rate rewards C_star C_h n z).map
        (Option.map (arrivalCoordinates rate)))
    else none
  have hg : Measurable g :=
    Measurable.ite (measurableSet_launchAtCut rate rewards C_star C_h n)
      (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ harrivals)
      measurable_const
  apply measurable_of_countable_fibers g hg
  intro z y he
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
      (cutBoundary rate rewards C_star C_h n z) z
  · by_cases hy : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
        (cutBoundary rate rewards C_star C_h n y) y
    · simp only [g, ite_eq_left hz, ite_eq_left hy, Option.some.injEq] at he
      simp only [precallReadout?, precallCells?, ite_eq_left hz, ite_eq_left hy]
      exact optional_run_congr rate _ _ he
    · simp only [g, ite_eq_left hz, ite_eq_right hy, reduceCtorEq] at he
  · by_cases hy : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
        (cutBoundary rate rewards C_star C_h n y) y
    · simp only [g, ite_eq_right hz, ite_eq_left hy, reduceCtorEq] at he
    · simp only [precallReadout?, precallCells?, ite_eq_right hz, ite_eq_right hy]

/-- Explicit terminal endpoint, with no specialization of a `Fin T` query. -/
theorem measurable_terminalReadout :
    Measurable (precallReadout? rate rewards C_star C_h p.T) :=
  measurable_precallReadout rate rewards C_star C_h p.T

/-- The cut on the actual optional incoming state is Borel. -/
theorem measurable_incomingObservation (t : Fin p.T) :
    Measurable (incomingObservation rate rewards C_star C_h t) :=
  Measurable.ite
    (measurableSet_le measurable_const (measurable_firstCallBoundary rate rewards C_star C_h))
    (ReferenceSourcePrefixHistoryFiltration.measurable_incoming rate rewards C_star C_h t)
    measurable_const

/-- All nine literal projections are jointly Borel on the whole original source. -/
theorem measurable_observation : Measurable (observation rate rewards C_star C_h) := by
  have hslots : Measurable (fun z : S =>
      fun n : Fin (p.T + 1) => slotObservation rate rewards C_star C_h n.val z) :=
    measurable_pi_iff.mpr (fun n => measurable_slotObservation rate rewards C_star C_h n.val)
  have hreadouts : Measurable (fun z : S =>
      fun n : Fin (p.T + 1) => precallReadout? rate rewards C_star C_h n.val z) :=
    measurable_pi_iff.mpr (fun n => measurable_precallReadout rate rewards C_star C_h n.val)
  have hincoming : Measurable (fun z : S =>
      fun t : Fin p.T => incomingObservation rate rewards C_star C_h t z) :=
    measurable_pi_iff.mpr (fun t => measurable_incomingObservation rate rewards C_star C_h t)
  exact measurable_selectedRow.prodMk
    ((ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).prodMk
      ((measurable_assignmentBegin rate rewards C_star C_h).prodMk
        ((ReferenceFirstCollectionSamplerCall.measurable_firstCollectionCall
          rate rewards C_star C_h).prodMk
          ((measurable_precallTrace rate rewards C_star C_h).prodMk
            ((measurable_precallRaw rate rewards C_star C_h).prodMk
              (hslots.prodMk (hreadouts.prodMk hincoming)))))))

open ReferenceFirstCollectionAssignmentNonRead
open CheckedAssignmentSample (AssignmentVector)

/-- The call trace comparison uses only the actual strict pre-call record
comparison; the assignment sampler at the endpoint is not compared. -/
theorem precallTrace_patch (z : S) (v : Fin p.T → AssignmentVector p) :
    precallTrace rate rewards C_star C_h
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      precallTrace rate rewards C_star C_h z := by
  unfold precallTrace
  rw [firstCollectionAssignmentPatch_firstCallBoundary,
    firstCollectionAssignmentPatch_physicalStart]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take,
      ReferenceCompletePhysicalHistory.completeSuffixRecords_length,
      firstCollectionAssignmentPatch_physicalStart]
  · intro k hk hk'
    simp only [List.length_map, List.length_take] at hk hk'
    have hkR : k < (R z).length := by omega
    obtain ⟨_, _, hc⟩ := calendar_comparison rate rewards C_star C_h z v k hkR (by omega)
    simpa only [List.getElem_map, List.getElem_take, Function.comp_apply] using
      (hc (by omega)).2.1.symm

/-- The actual optional slot coordinates are unchanged, without filling any
missing numerical input or dropping an enabled zero-arrival date. -/
theorem slotObservation_patch (n : ℕ) (z : S) (v : Fin p.T → AssignmentVector p) :
    slotObservation rate rewards C_star C_h n
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      slotObservation rate rewards C_star C_h n z := by
  unfold slotObservation
  rw [firstCollectionAssignmentPatch_precallSlots]

/-- The incoming-state query is retained through the endpoint, and the
observation alone is absent beyond it. -/
theorem incomingObservation_patch (t : Fin p.T) (z : S)
    (v : Fin p.T → AssignmentVector p) :
    incomingObservation rate rewards C_star C_h t
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      incomingObservation rate rewards C_star C_h t z := by
  unfold incomingObservation
  rw [firstCollectionAssignmentPatch_firstCallBoundary]
  by_cases ht : t.val ≤ b z
  · rw [ite_eq_left ht, ite_eq_left ht]
    exact incoming_eq_through_first_call rate rewards C_star C_h t z v ht
  · rw [ite_eq_right ht, ite_eq_right ht]

/-- Joint deterministic non-read for the one ordinary product observation.
All full `K+1` assignment vectors may be replaced in the unused original
block. This is an equality of observations, not a source-law assertion. -/
theorem observation_patch (z : S) (v : Fin p.T → AssignmentVector p) :
    observation rate rewards C_star C_h
        (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      observation rate rewards C_star C_h z := by
  have hq := (firstCollectionAssignmentPatch_private_and_id rate rewards C_star C_h z v).2.2
  have ha := firstCollectionAssignmentPatch_assignmentBegin rate rewards C_star C_h z v
  have hslots : (fun n : Fin (p.T + 1) => slotObservation rate rewards C_star C_h n.val
      (firstCollectionAssignmentPatch rate rewards C_star C_h z v)) =
      (fun n : Fin (p.T + 1) => slotObservation rate rewards C_star C_h n.val z) :=
    funext (fun n => slotObservation_patch rate rewards C_star C_h n.val z v)
  have hreadouts : (fun n : Fin (p.T + 1) => precallReadout? rate rewards C_star C_h n.val
      (firstCollectionAssignmentPatch rate rewards C_star C_h z v)) =
      (fun n : Fin (p.T + 1) => precallReadout? rate rewards C_star C_h n.val z) :=
    funext (fun n => firstCollectionAssignmentPatch_precallReadout
      rate rewards C_star C_h n.val z v)
  have hincoming : (fun t : Fin p.T => incomingObservation rate rewards C_star C_h t
      (firstCollectionAssignmentPatch rate rewards C_star C_h z v)) =
      (fun t : Fin p.T => incomingObservation rate rewards C_star C_h t z) :=
    funext (fun t => incomingObservation_patch rate rewards C_star C_h t z v)
  unfold observation
  rw [hq, firstCollectionAssignmentPatch_physicalStart]
  change assignmentBegin rate rewards C_star C_h
    (firstCollectionAssignmentPatch rate rewards C_star C_h z v) =
      assignmentBegin rate rewards C_star C_h z at ha
  rw [ha, firstCollectionAssignmentPatch_firstCollectionCall,
    precallTrace_patch, hslots, hreadouts, hincoming]
  unfold precallRaw
  rw [firstCollectionAssignmentPatch_firstCallBoundary,
    firstCollectionAssignmentPatch_physicalStart,
    precall_rawDiagnostic_eq]

open ReferenceFirstCollectionAuxiliarySeeds
  (actualCollectionCallCell auxiliarySourceLaw auxiliaryBlock auxiliaryCellLaw AuxiliaryArray)

/-- The finite row and unused-block endpoint constraints are literal original
source projections. Their endpoints are allowed to be the genuine horizon. -/
def calendarConstraints (q0 : Fin (M p)) (a0 b0 : Fin (p.T + 1)) : Set S :=
  {z | selectedRowIndex p z = q0 ∧
    assignmentBegin rate rewards C_star C_h z = a0.val ∧ b z = b0.val}

/-- A finite retained-calendar cell intersected with the actual first-call
cutoff/time event. Failure of the checked sampler is not excluded. -/
def calendarCell (q0 : Fin (M p)) (a0 b0 : Fin (p.T + 1)) (u t : Fin p.T) : Set S :=
  calendarConstraints rate rewards C_star C_h q0 a0 b0 ∩
    actualCollectionCallCell rate rewards C_star C_h u t

theorem measurableSet_calendarConstraints (q0 : Fin (M p)) (a0 b0 : Fin (p.T + 1)) :
    MeasurableSet (calendarConstraints rate rewards C_star C_h q0 a0 b0) :=
  ((measurableSet_singleton q0).preimage measurable_selectedRow).inter
    (((measurableSet_singleton a0.val).preimage
      (measurable_assignmentBegin rate rewards C_star C_h)).inter
      ((measurableSet_singleton b0.val).preimage
        (measurable_firstCallBoundary rate rewards C_star C_h)))

/-- Each requested literal finite cell is Borel on the whole original source. -/
theorem measurableSet_calendarCell (q0 : Fin (M p)) (a0 b0 : Fin (p.T + 1))
    (u t : Fin p.T) :
    MeasurableSet (calendarCell rate rewards C_star C_h q0 a0 b0 u t) :=
  (measurableSet_calendarConstraints rate rewards C_star C_h q0 a0 b0).inter
    (ReferenceFirstCollectionAuxiliarySeeds.measurableSet_actualCollectionCallCell
      rate rewards C_star C_h u t)

/-- The whole retained observation and the independent analytical auxiliary
block have their joint product law on each literal calendar cell. This is an
unnormalized identity for EVERY source set, including null and empty cells.

The auxiliary trigger refresh at `u.val - 1` belongs to the separate array.
Both auxiliary labels on `[u.val,t.val)` are retained by `auxiliaryBlock`.
No assertion is made about the physical unused assignment block or the
physical sampler vector at the invocation date. -/
theorem observation_auxiliaryBlock_jointLaw
    (q0 : Fin (M p)) (a0 b0 : Fin (p.T + 1)) (u t : Fin p.T) (Aset : Set S) :
    ((auxiliarySourceLaw p).restrict
      ((Aset ∩ calendarCell rate rewards C_star C_h q0 a0 b0 u t) ×ˢ Set.univ)).map
        (fun w : S × AuxiliaryArray p =>
          (observation rate rewards C_star C_h w.1, auxiliaryBlock u t w.2)) =
      (((sourceInputLaw p).restrict
        (Aset ∩ calendarCell rate rewards C_star C_h q0 a0 b0 u t)).map
          (observation rate rewards C_star C_h)).prod (auxiliaryCellLaw u t) := by
  let B := Aset ∩ calendarConstraints rate rewards C_star C_h q0 a0 b0
  let E := B ∩ actualCollectionCallCell rate rewards C_star C_h u t
  have hjoint := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryBlock_jointLaw_on_actualCollectionCallCell
    rate rewards C_star C_h u t B
  have hfirst : Measurable (fun w : S × AuxiliaryArray p =>
      (w.1, auxiliaryBlock u t w.2)) :=
    measurable_id.prodMap
      (ReferenceFirstCollectionAuxiliarySeeds.measurable_auxiliaryBlock u t)
  have hsecond : Measurable
      (Prod.map (observation rate rewards C_star C_h)
        (id : (ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryCellIndex u t →
          ContinuousControlSlice.Scalar) → _)) :=
    (measurable_observation rate rewards C_star C_h).prodMap measurable_id
  have hresult :
      ((auxiliarySourceLaw p).restrict (E ×ˢ Set.univ)).map
        (fun w : S × AuxiliaryArray p =>
          (observation rate rewards C_star C_h w.1, auxiliaryBlock u t w.2)) =
      (((sourceInputLaw p).restrict E).map
        (observation rate rewards C_star C_h)).prod (auxiliaryCellLaw u t) := by
    calc
      _ = (((auxiliarySourceLaw p).restrict (E ×ˢ Set.univ)).map
          (fun w : S × AuxiliaryArray p => (w.1, auxiliaryBlock u t w.2))).map
            (Prod.map (observation rate rewards C_star C_h) id) := by
        rw [Measure.map_map hsecond hfirst]
        rfl
      _ = (((sourceInputLaw p).restrict E).prod (auxiliaryCellLaw u t)).map
          (Prod.map (observation rate rewards C_star C_h) id) := by rw [hjoint]
      _ = _ := by
        rw [← Measure.map_prod_map _ _ (measurable_observation rate rewards C_star C_h)
          measurable_id, Measure.map_id]
  simpa only [E, B, calendarCell, Set.inter_assoc] using hresult

/-- The independent enlargement has precisely the original physical marginal. -/
theorem auxiliarySourceLaw_original_marginal :
    (auxiliarySourceLaw p).map Prod.fst = sourceInputLaw p :=
  ReferenceFirstCollectionAuxiliarySeeds.auxiliarySourceLaw_physical_marginal p

end Bandits.Support.ReferenceFirstCollectionDeferredCalendarProduct

end
