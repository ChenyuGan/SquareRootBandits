/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedNextPhysicalReadout

/-!
# Strict-prior retained gate at the original first-call successor

The current AFTER readout is the existing strict prefix readout at the next
calendar date. The prefix contains every original optional date, and appends
the actual current live cell without restarting the inherited queue. This
identity supplies predictability of the literal corrected retained event on
the whole original source space.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:352-431`,
`04_slow_fast_learner.tex:140-188,245-278`, `06_interruptions.tex:355-426`,
and `appendix_a_local_protocol.tex:28-79`.

These are internal deterministic information results, not a conditional
recording law, a physical/logical queue identification, or manuscript closure.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open ReferenceSourcePrefixHistoryFiltration
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCorrectedNextRetainedGate

variable {p : Parameters}

local notation "X" => BootstrapPrivateRoundStreams.SourceInput p

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local instance sourceInputMeasurableSpace : MeasurableSpace X := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance optionNatMeasurableSpace : MeasurableSpace (Option ℕ) :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.optionNatMeasurableSpace

local instance optionNatDiscrete : DiscreteMeasurableSpace (Option ℕ) := by
  constructor
  intro s
  let e := Equiv.optionEquivSumPUnit ℕ
  exact ⟨e '' s, measurableSet_sum_iff.mpr
    ⟨MeasurableSet.of_discrete, MeasurableSet.of_discrete⟩,
    e.injective.preimage_image s⟩

local notation "E" => ReferenceCalendarCollectionCallControlLaw.firstCell
  rate rewards C_star C_h
local notation "N" => ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
local notation "oldFreeze" => ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
local notation "pastCells" => ReferenceFirstCollectionCurrentRetainedGate.pastCells?
local notation "pastSlots" => ReferenceFirstCollectionCurrentRetainedGate.pastSlots
local notation "cell0" => ReferenceFirstCollectionCurrentRetainedGate.cell0
local notation "currentCell" => ReferenceFirstCollectionCurrentNumericalCell.currentCell
local notation "prefixReadout" => ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
local notation "afterReadout" => ReferenceFirstCollectionCurrentQueueReadout.after?

private theorem live_readout_zero
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (s : ℕ) (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
  obtain ⟨selected, ho, hselection, hbase, hlive, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some s r c hc
  have hz : 0 < selected.view.payload.sigma.val := by omega
  unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
  simp only [hselection, hz, hlive, and_self, ite_true, dite_eq_left ho]
  exact congrArg some hcell.symm

/-- At the original invocation the strict physical-start live query and the
zero-baseline generic calendar query name exactly the same actual cell. -/
theorem firstCell_current_eq_calendar (u t : Fin p.T) (x : X)
    (hx : x ∈ E u t) :
    currentCell rate rewards C_star C_h t x =
      (actualRecord rate rewards C_star C_h t x).bind (cell0 rate) := by
  obtain ⟨r, _hr, har, _ht, hchosen⟩ :=
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_firstReplacement_record
      rate rewards C_star C_h u t x hx
  have hsome : (currentCell rate rewards C_star C_h t x).isSome = true :=
    (ReferenceFirstCollectionCurrentNumericalCell.currentCell_isSome_iff
      rate rewards C_star C_h u t x hx).mpr ⟨r, har, hchosen⟩
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
  have hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h) r =
        some c := by
    simpa only [ReferenceFirstCollectionCurrentNumericalCell.currentCell,
      har, Option.bind_some] using hc
  have hz := live_readout_zero rate r _ c hlive
  simp only [hc, har, Option.bind_some,
    ReferenceFirstCollectionCurrentRetainedGate.cell0, hz, Option.some_or]

/-- The successor strict prefix appends the actual current cell. A missing
inherited slot still makes the entire optional prefix absent. -/
theorem firstCell_pastCells_successor (u t : Fin p.T)
    (hq : t.val + 1 < p.T) (x : X) (hx : x ∈ E u t) :
    pastCells rate rewards C_star C_h ⟨t.val + 1, hq⟩ x =
      (pastCells rate rewards C_star C_h t x).bind (fun L =>
        (currentCell rate rewards C_star C_h t x).map (fun c => L ++ [c])) := by
  obtain ⟨r, _hr, har, _ht, _hchosen⟩ :=
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_firstReplacement_record
      rate rewards C_star C_h u t x hx
  have hlaunch : actualLaunchBy rate rewards C_star C_h t.val x := by
    by_contra hnot
    rw [actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t x hnot] at har
    cases har
  have hlaunchNext : actualLaunchBy rate rewards C_star C_h (t.val + 1) x :=
    ⟨hlaunch.1, hlaunch.2.trans (Nat.le_succ _)⟩
  have hindex : t.val + 1 -
      ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h =
        (t.val - ReferenceCompletePhysicalHistory.physicalStart
          rate x rewards C_star C_h) + 1 := by
    have hs := hlaunch.2
    omega
  have hslots : pastSlots rate rewards C_star C_h ⟨t.val + 1, hq⟩ x =
      pastSlots rate rewards C_star C_h t x ++
        [(currentCell rate rewards C_star C_h t x)] := by
    rw [firstCell_current_eq_calendar rate rewards C_star C_h u t x hx]
    simp only [ReferenceFirstCollectionCurrentRetainedGate.pastSlots,
      hindex, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      actualRecord, ite_eq_left hlaunch.2]
  simp only [ReferenceFirstCollectionCurrentRetainedGate.pastCells?,
    ite_eq_left hlaunch, ite_eq_left hlaunchNext, hslots, List.mapM_append,
    List.mapM_cons, List.mapM_nil, id_eq]
  cases (pastSlots rate rewards C_star C_h t x).mapM id <;>
    cases currentCell rate rewards C_star C_h t x <;> rfl

/-- The AFTER overflow flag is a strict-prior observation at the immediate
successor, including the first detecting update and all accepted histories. -/
theorem firstCell_after_eq_successor_prefix (u t : Fin p.T)
    (hq : t.val + 1 < p.T) (x : X) (hx : x ∈ E u t) :
    afterReadout rate rewards C_star C_h t x =
      prefixReadout rate rewards C_star C_h ⟨t.val + 1, hq⟩ x := by
  rw [ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?,
    firstCell_pastCells_successor rate rewards C_star C_h u t hq x hx]
  unfold ReferenceFirstCollectionCurrentQueueReadout.after?
  cases hL : pastCells rate rewards C_star C_h t x with
  | none => rfl
  | some L =>
      cases hc : currentCell rate rewards C_star C_h t x with
      | none => rfl
      | some c =>
          simp only [Option.bind_some, Option.map_some]
          congr 1
          simp only [RecordedQueueRun.run, RecordedEpisodeStability.execute_append,
            RecordedQueueRun.execute]

variable (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T)

local notation "C" => Set.ofPred (fun x : X => x ∈ E u t ∧ ∃ g,
  oldFreeze rate rewards C_star C_h t x = some g ∧ t.val + 1 < g)

/-- The literal corrected branch is measurable in the strict successor field.
No branch, launch, or domain assertion is assumed on the source input. -/
theorem firstCell_successorBranch_measurable :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 2)] C := by
  have hcell : MeasurableSet (E u t) := by
    simpa only [ReferenceCalendarCollectionCallControlLaw.firstCell] using
      ReferenceFirstCollectionSamplerCall.measurableSet_firstCollectionCall_cell
        rate rewards C_star C_h u t
  have hfreeze : MeasurableSet {x : X | ∃ g,
      oldFreeze rate rewards C_star C_h t x = some g ∧ t.val + 1 < g} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro g
    exact (measurableSet_eq_fun
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_oldFreezeAt?
        rate rewards C_star C_h t) measurable_const).inter (MeasurableSet.const _)
  have hglobal : MeasurableSet C := hcell.inter hfreeze
  have hfactor (x : X) : x ∈ C ↔ sourcePrefix control0 (t.val + 1) x ∈ C := by
    have hid := sourcePrefix_sourcePrefix control0 (t.val + 1) (t.val + 1) le_rfl x
    constructor
    · rintro ⟨hx, g, hg, hlt⟩
      obtain ⟨hy, hgy, hlty⟩ :=
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.corrected_branch_prefix_congr
          rate rewards C_star C_h control0 u t x
          (sourcePrefix control0 (t.val + 1) x) hid.symm hx g hg hlt
      exact ⟨hy, g, hgy, hlty⟩
    · rintro ⟨hy, g, hg, hlt⟩
      obtain ⟨hx, hgx, hltx⟩ :=
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.corrected_branch_prefix_congr
          rate rewards C_star C_h control0 u t
          (sourcePrefix control0 (t.val + 1) x) x hid hy g hg hlt
      exact ⟨hx, g, hgx, hltx⟩
  rw [show t.val + 2 = (t.val + 1) + 1 by omega, sourcePrefixFiltration_succ]
  exact ⟨C, hglobal, by ext x; exact (hfactor x).symm⟩

private theorem measurable_option_elim {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (f : A → B) (hf : Measurable f) (b : B) :
    Measurable (fun o : Option A => o.elim b f) := by
  have hs : Measurable (Equiv.optionEquivSumPUnit A) := comap_measurable _
  convert (hf.sumElim measurable_const).comp hs using 1
  funext o
  cases o <;> rfl

local notation "G" hq => Set.ofPred (fun x : X => x ∈ C ∧
  (∃ y, afterReadout rate rewards C_star C_h t x = some y ∧
    Prod.fst (Prod.snd y) = false) ∧
  ∃ xi, N rate rewards C_star C_h t hq x = some (true, xi))

/-- Strict-prior predictability of the actual inherited AFTER-queue retained
and enabled event, on the whole original source space. -/
theorem retainedGate_measurable (hq : t.val + 1 < p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 2)] (G hq) := by
  let Fq := sourcePrefixFiltration control0 (t.val + 2)
  have hC : MeasurableSet[Fq] C :=
    firstCell_successorBranch_measurable rate rewards C_star C_h control0 u t
  have hH : MeasurableSet[Fq]
      (ReferenceFirstCollectionCurrentRetainedGate.H
        rate rewards C_star C_h ⟨t.val + 1, hq⟩) :=
    ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
      rate rewards C_star C_h control0 ⟨t.val + 1, hq⟩
  have hp := ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCellParameters_measurable
    rate rewards C_star C_h control0 u t hq
  have he : Measurable[Fq] (fun x : X =>
      (if x ∈ E u t then N rate rewards C_star C_h t hq x else none).elim
        false Prod.fst) :=
    (measurable_option_elim Prod.fst measurable_fst false).comp hp
  have hs := (hC.inter hH).inter ((MeasurableSet.singleton true).preimage he)
  convert hs using 1
  ext x
  change (x ∈ C ∧
      (∃ y, afterReadout rate rewards C_star C_h t x = some y ∧ y.2.1 = false) ∧
      ∃ xi, N rate rewards C_star C_h t hq x = some (true, xi)) ↔
    (x ∈ C ∧ x ∈ ReferenceFirstCollectionCurrentRetainedGate.H
      rate rewards C_star C_h ⟨t.val + 1, hq⟩) ∧
    (if x ∈ E u t then N rate rewards C_star C_h t hq x else none).elim
      false Prod.fst = true
  by_cases hx : x ∈ C
  · rw [ite_eq_left hx.1,
      firstCell_after_eq_successor_prefix rate rewards C_star C_h u t hq x hx.1]
    simp only [hx, true_and, ReferenceFirstCollectionCurrentRetainedGate.H,
      Set.mem_ofPred_eq]
    apply and_congr Iff.rfl
    cases hp : N rate rewards C_star C_h t hq x with
    | none => simp only [Option.elim_none, Bool.false_eq_true, reduceCtorEq, exists_false]
    | some parameters =>
        rcases parameters with ⟨enabled, xi⟩
        simp only [Option.elim_some, Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨_, hb, _⟩
          exact hb
        · intro hb
          exact ⟨xi, hb, rfl⟩
  · simp only [hx, false_and]

end Bandits.Support.ReferenceFirstCollectionCorrectedNextRetainedGate
