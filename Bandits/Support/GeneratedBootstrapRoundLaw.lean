/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationPrefixInvariance
public import Bandits.Support.ReferenceInitializationMeasurability
public import Bandits.Support.BootstrapModeService
public import Bandits.Support.CompleteRowStoppingLaw
public import Bandits.Support.PrivateRoundFreshness

/-!
# Original current-round coordinates against the generated bootstrap past

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-38,55-113`,
`appendix_b_communication.tex:398-445,638-656`, and `08_main_theorem.tex:26-42`.

The measure is the original complete-row/private product, with IDs and rounded
rewards fixed before publication conditioning. The past retains all block
triples, the separate private J scalar and target stream, but only strict-past
calendar entries and player-round scalars. A completion is used solely to
construct a measurable factor of this past; pointwise reconstruction eliminates
it from the actual generated descriptor and its cylinder law.

This is internal product-stream mathematics, with no publication-conditioned
freshness, block-coin conditional law, chronological mean, or source closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.GeneratedBootstrapRoundLaw

open MeasureTheory
open ConstructorDimensions BootstrapDimensions CompletePublicTable
open BootstrapPrivateRoundStreams PrivateRoundFreshness
open ReferenceInitializationRun ReferenceInitializationCausality
open ReferenceInitializationMeasurability
open scoped Classical

/-- The original random input, before publication conditioning. -/
abbrev Coordinates (p : Parameters) := CompleteRow p × ExtendedPrivateCoordinates p

/-- The law is exactly the accepted row law times the accepted private law. -/
def originalLaw (p : Parameters) : Measure (Coordinates p) :=
  (completeRowMeasure p).prod (extendedPrivateLaw p)

instance originalLaw_probability (p : Parameters) : IsProbabilityMeasure (originalLaw p) := by
  unfold originalLaw
  infer_instance

/-- The calendar cutoff at the original current round (zero based). -/
def cutoff (p : Parameters) (t : Fin p.T) : Fin (p.T + 1) :=
  ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩

/-- Literal public strict past paired with the accepted private past view. -/
abbrev Past (p : Parameters) (t : Fin p.T) :=
  CompleteRowStoppingLaw.PastArray p (cutoff p t) × PastView p t

/-- The exact past marginal, in public-then-private order. -/
def pastLaw (p : Parameters) (t : Fin p.T) : Measure (Past p t) :=
  (CompleteRowStoppingLaw.pastArrayLaw p (cutoff p t)).prod (pastViewLaw p t)

instance pastLaw_probability (p : Parameters) (t : Fin p.T) :
    IsProbabilityMeasure (pastLaw p t) := by
  unfold pastLaw
  infer_instance

/-- Both current vectors retain their entire original coordinates. -/
abbrev Current (p : Parameters) :=
  BootstrapModeService.RoundCoordinates p × CurrentRoundScalars p

/-- Public forward/control law followed by the same original scalar per player. -/
def currentLaw (p : Parameters) : Measure (Current p) :=
  (BootstrapModeService.roundCoordinatesMeasure p).prod (currentRoundScalarLaw p)

instance currentLaw_probability (p : Parameters) : IsProbabilityMeasure (currentLaw p) := by
  unfold currentLaw
  infer_instance

/-- The actual coordinate projection W, with no generated history supplied. -/
def past (p : Parameters) (t : Fin p.T) (e : Coordinates p) : Past p t :=
  ((CompleteRowStoppingLaw.calendarSplitEquiv p (cutoff p t)
    (CompleteRowStoppingLaw.calendarizeRowEquiv p e.1)).1,
    (extendedPrivateRoundSplitEquiv p t e.2).1)

/-- Original current complete row entry and original player scalar vector. -/
def current (p : Parameters) (t : Fin p.T) (e : Coordinates p) : Current p :=
  (BootstrapModeService.roundCoordinates p t e.1,
    fun i => BootstrapPhysicalInput.playerRoundScalarAt p e.2 i t)

private theorem measurePreserving_pair_reorder
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (a : Measure α) (b : Measure β) (c : Measure γ) (d : Measure δ)
    [IsProbabilityMeasure a] [IsProbabilityMeasure b]
    [IsProbabilityMeasure c] [IsProbabilityMeasure d] :
    MeasurePreserving (fun z : (α × β) × (γ × δ) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      ((a.prod b).prod (c.prod d)) ((a.prod c).prod (b.prod d)) := by
  have h₁ := measurePreserving_prodAssoc a b (c.prod d)
  have h₂ := (MeasurePreserving.id a).prod (measurePreserving_prodAssoc b c d).symm
  have h₃ := (MeasurePreserving.id a).prod
    ((Measure.measurePreserving_swap (μ := b) (ν := c)).prod (MeasurePreserving.id d))
  have h₄ := (MeasurePreserving.id a).prod (measurePreserving_prodAssoc c b d)
  have h₅ := (measurePreserving_prodAssoc a c (b.prod d)).symm
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

/-- Exact pushforward of (W,r,v). Future row and scalar coordinates have been
integrated out, and the displayed product order is literal. -/
theorem past_current_measurePreserving (p : Parameters) (t : Fin p.T) :
    MeasurePreserving (fun e => (past p t e, current p t e)) (originalLaw p)
      ((pastLaw p t).prod (currentLaw p)) := by
  let σ := cutoff p t
  let j : CompleteRowStoppingLaw.FutureIndex p σ := ⟨t, Nat.lt_irrefl _⟩
  have hrowSplit := (CompleteRowStoppingLaw.measurePreserving_calendarSplit p σ).comp
    (CompleteRowStoppingLaw.measurePreserving_calendarizeRow p)
  have heval : MeasurePreserving (Function.eval j)
      (CompleteRowStoppingLaw.futureArrayLaw p σ)
      (BootstrapModeService.roundCoordinatesMeasure p) :=
    measurePreserving_eval (fun _ => CompleteRowStoppingLaw.calendarEntryLaw p) j
  have hrow := ((MeasurePreserving.id
    (CompleteRowStoppingLaw.pastArrayLaw p σ)).prod heval).comp hrowSplit
  have hprivate := ((MeasurePreserving.id (pastViewLaw p t)).prod
    (measurePreserving_fst (μ := currentRoundScalarLaw p)
      (ν := futureRoundScalarLaw p t))).comp
        (extendedPrivateRoundSplit_measurePreserving p t)
  exact (measurePreserving_pair_reorder
    (CompleteRowStoppingLaw.pastArrayLaw p σ)
    (BootstrapModeService.roundCoordinatesMeasure p) (pastViewLaw p t)
    (currentRoundScalarLaw p)).comp (hrow.prod hprivate)

/-- The exact map equality version of the original joint law. -/
theorem past_current_map (p : Parameters) (t : Fin p.T) :
    (originalLaw p).map (fun e => (past p t e, current p t e)) =
      (pastLaw p t).prod (currentLaw p) :=
  (past_current_measurePreserving p t).map_eq

/-- Measurable completion of W using arbitrary fixed omitted coordinates.
It is only a proof device, not an alternative physical semantics. -/
def complete (p : Parameters) (t : Fin p.T) (e₀ : Coordinates p)
    (w : Past p t) : Coordinates p :=
  ((CompleteRowStoppingLaw.calendarizeRowEquiv p).symm
    ((CompleteRowStoppingLaw.calendarSplitEquiv p (cutoff p t)).symm
      (w.1, (CompleteRowStoppingLaw.calendarSplitEquiv p (cutoff p t)
        (CompleteRowStoppingLaw.calendarizeRowEquiv p e₀.1)).2)),
    (extendedPrivateRoundSplitEquiv p t).symm
      (w.2, (extendedPrivateRoundSplitEquiv p t e₀.2).2))

theorem measurable_complete (p : Parameters) (t : Fin p.T) (e₀ : Coordinates p) :
    Measurable (complete p t e₀) := by
  exact ((CompleteRowStoppingLaw.calendarizeRowEquiv p).symm.measurable.comp
    ((CompleteRowStoppingLaw.calendarSplitEquiv p (cutoff p t)).symm.measurable.comp
      (measurable_fst.prodMk measurable_const))).prodMk
    ((extendedPrivateRoundSplitEquiv p t).symm.measurable.comp
      (measurable_snd.prodMk measurable_const))

theorem past_complete (p : Parameters) (t : Fin p.T) (e₀ : Coordinates p)
    (w : Past p t) : past p t (complete p t e₀ w) = w := by
  simp only [past, complete, MeasurableEquiv.apply_symm_apply]

/-- Fixed parameters are inserted by the accepted adapter, not sampled or
conditioned upon. -/
def input (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (e : Coordinates p) : ReferenceInitializationRun.Input p :=
  inputOfCoordinates p C_star C_h eta rewards (ids, e)

/-- The actual boundary, full labelled latent profile, target, and existing
physical pre-choice state. Only incoming profile entries describe physical
bootstrap choices. -/
abbrev Descriptor (p : Parameters) :=
  Boundary p × (PrivateSourceStreams.BlockDrawProfile p ×
    (Fin p.K × BootstrapPhysicalBlock.State p))

private theorem stateCoordinates_injective (p : Parameters) :
    Function.Injective (BootstrapBlockCausality.stateCoordinates (p := p)) := by
  intro a b h
  cases a
  cases b
  cases h
  rfl

instance modeCountable : Countable BootstrapPhysicalBlock.Mode := by
  apply Function.Injective.countable
    (f := fun m : BootstrapPhysicalBlock.Mode => match m with
      | .discover => false
      | .multicast => true)
  intro a b h
  cases a <;> cases b <;> simp_all

instance stateCountable (p : Parameters) : Countable (BootstrapPhysicalBlock.State p) :=
  (stateCoordinates_injective p).countable

/-- The existing state sigma algebra separates its exact list/mode/log atoms.
No new discrete state semantics is introduced. -/
instance stateMeasurableSingletonClass (p : Parameters) :
    MeasurableSingletonClass (BootstrapPhysicalBlock.State p) where
  measurableSet_singleton st := by
    have he : ({st} : Set (BootstrapPhysicalBlock.State p)) =
        BootstrapBlockCausality.stateCoordinates ⁻¹'
          {BootstrapBlockCausality.stateCoordinates st} := by
      ext a
      exact (stateCoordinates_injective p).eq_iff.symm
    rw [he]
    exact (comap_measurable _ (measurableSet_singleton _))

/-- No descriptor is produced when the accepted advance does not process a
block. Both stopped and exhausted guards are kept literally. -/
def descriptorAtBoundary (p : Parameters) (x : ReferenceInitializationRun.Input p)
    (b : Boundary p) (t : Fin p.T) : Option (Descriptor p) :=
  if b.crossing = none then
    if h : b.completed < n_boot p then
      some (b, (BootstrapPhysicalInput.currentBlockDrawProfile p (nextBlock b h)
        b.numerators b.weight_ge_one x.coordinates,
        ((physical x b h).target, BootstrapPhysicalBlock.run (physical x b h) t.val)))
    else none
  else none

/-- Exact characterization of a processed descriptor: its boundary and every
recorded field come from the existing guarded physical map. -/
theorem descriptorAtBoundary_eq_some_iff (p : Parameters)
    (x : ReferenceInitializationRun.Input p) (b c : Boundary p) (t : Fin p.T)
    (d : PrivateSourceStreams.BlockDrawProfile p) (a : Fin p.K)
    (st : BootstrapPhysicalBlock.State p) :
    descriptorAtBoundary p x b t = some (c, (d, (a, st))) ↔
      b = c ∧ b.crossing = none ∧ ∃ h : b.completed < n_boot p,
        BootstrapPhysicalInput.currentBlockDrawProfile p (nextBlock b h)
          b.numerators b.weight_ge_one x.coordinates = d ∧
        (physical x b h).target = a ∧ BootstrapPhysicalBlock.run (physical x b h) t.val = st := by
  unfold descriptorAtBoundary
  by_cases hc : b.crossing = none
  · rw [ite_eq_left hc]
    by_cases h : b.completed < n_boot p
    · rw [dite_eq_left h]
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨hb, hd, ha, hs⟩
        exact ⟨hb, hc, h, hd, ha, hs⟩
      · rintro ⟨hb, _, h', hd, ha, hs⟩
        exact ⟨hb, hd, ha, hs⟩
    · rw [dite_eq_right h]
      constructor
      · intro he
        cases he
      · rintro ⟨_, _, h', _⟩
        exact (h h').elim
  · rw [ite_eq_right hc]
    constructor
    · intro he
      cases he
    · rintro ⟨_, hc', _⟩
      exact (hc hc').elim

/-- The descriptor of the original generated opportunity, without a physical
trace after launch. -/
def descriptor (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (t : Fin p.T) (e : Coordinates p) : Option (Descriptor p) :=
  let x := input p ids rewards C_star C_h eta e
  descriptorAtBoundary p x (ReferenceInitializationRun.run x s.val) t

section Generated

variable {p : Parameters} (ids : IDArray p)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
  (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
  (s : Fin (n_boot p)) (t : Fin p.T)

/-- Absence is exactly the stopped branch at this valid opportunity. There
is no manufactured physical continuation following a launch. -/
theorem descriptor_eq_none_iff (e : Coordinates p) :
    descriptor p ids rewards C_star C_h eta s t e = none ↔
      (ReferenceInitializationRun.run
        (input p ids rewards C_star C_h eta e) s.val).crossing ≠ none := by
  let x := input p ids rewards C_star C_h eta e
  by_cases hc : (ReferenceInitializationRun.run x s.val).crossing = none
  · have he := (run_progress x s.val s.isLt.le).resolve_left
      (show ¬ (ReferenceInitializationRun.run x s.val).crossing.isSome = true by
        rw [hc]
        exact Bool.false_ne_true)
    have h : (ReferenceInitializationRun.run x s.val).completed < n_boot p := by
      rw [he]
      exact s.isLt
    change descriptorAtBoundary p x (ReferenceInitializationRun.run x s.val) t = none ↔
      (ReferenceInitializationRun.run x s.val).crossing ≠ none
    simp only [descriptorAtBoundary, hc, ite_true, dite_eq_left h, reduceCtorEq,
      ne_eq, not_true_eq_false]
  · change descriptorAtBoundary p x (ReferenceInitializationRun.run x s.val) t = none ↔
      (ReferenceInitializationRun.run x s.val).crossing ≠ none
    simp only [descriptorAtBoundary, hc, ite_false, ne_eq, not_false_eq_true]

/-- The current block starts no later than its member calendar round. -/
theorem elapsed_le_of_mem_calendarBlock (ht : t ∈ calendarBlock p s) :
    elapsed p s.val ≤ t.val := by
  have h := ((mem_calendarBlock_iff p s t).mp ht).1
  exact (Nat.min_le_right _ _).trans h

/-- Equality of W supplies every read coordinate for the actual generated
boundary, including all original source labels. -/
theorem runPrefixInputEq_of_past_eq (ht : t ∈ calendarBlock p s)
    (e f : Coordinates p) (hw : past p t e = past p t f) :
    runPrefixInputEq (input p ids rewards C_star C_h eta e)
      (input p ids rewards C_star C_h eta f) s.val := by
  have hcut := elapsed_le_of_mem_calendarBlock s t ht
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hqt : q.val < t.val := hq.trans_le hcut
    have he := congrArg (fun w : Past p t => w.1 ⟨q, hqt⟩) hw
    exact ⟨fun u => congrArg (fun z => z.1 u) he, congrArg Prod.snd he⟩
  · intro k _ j
    exact congrArg (fun w : Past p t => w.2.1.1 k j) hw
  · intro k _
    exact congrArg (fun w : Past p t => w.2.2.2 k) hw
  · intro i q hq
    have hqt : q < t := hq.trans_le hcut
    exact congrArg (fun w : Past p t => w.2.2.1 ⟨⟨(i, q), hqt.le⟩, hqt⟩) hw

/-- On a processed opportunity the generated boundary really is at s, with
its actual no-crossing guard. -/
theorem processed_completed (e : Coordinates p)
    (hc : (ReferenceInitializationRun.run
      (input p ids rewards C_star C_h eta e) s.val).crossing = none) :
    (ReferenceInitializationRun.run (input p ids rewards C_star C_h eta e) s.val).completed =
      s.val := by
  apply (run_progress (input p ids rewards C_star C_h eta e) s.val s.isLt.le).resolve_left
  rw [hc]
  exact Bool.false_ne_true

/-- The actual physical block label is s whenever this opportunity is processed. -/
theorem processed_nextBlock (e : Coordinates p)
    (hc : (ReferenceInitializationRun.run
      (input p ids rewards C_star C_h eta e) s.val).crossing = none)
    (h : (ReferenceInitializationRun.run
      (input p ids rewards C_star C_h eta e) s.val).completed < n_boot p) :
    nextBlock (ReferenceInitializationRun.run
      (input p ids rewards C_star C_h eta e) s.val) h = s := by
  apply Fin.ext
  exact processed_completed ids rewards C_star C_h eta s e hc

/-- Full generated descriptor equality follows from W equality. No boundary,
history, equal-state, or independence premise is supplied. -/
theorem descriptor_eq_of_past_eq (ht : t ∈ calendarBlock p s)
    (e f : Coordinates p) (hw : past p t e = past p t f) :
    descriptor p ids rewards C_star C_h eta s t e =
      descriptor p ids rewards C_star C_h eta s t f := by
  let x := input p ids rewards C_star C_h eta e
  let y := input p ids rewards C_star C_h eta f
  have hb : ReferenceInitializationRun.run x s.val = ReferenceInitializationRun.run y s.val :=
    ReferenceInitializationPrefixInvariance.run_eq_of_runPrefixInputEq x y s.val
      (runPrefixInputEq_of_past_eq ids rewards C_star C_h eta s t ht e f hw)
  change descriptorAtBoundary p x (ReferenceInitializationRun.run x s.val) t =
    descriptorAtBoundary p y (ReferenceInitializationRun.run y s.val) t
  rw [← hb]
  unfold descriptorAtBoundary
  split_ifs with hc h
  · have hbase : x.coordinates.1 = y.coordinates.1 :=
      congrArg (fun w : Past p t => w.2.1) hw
    have htarget : ∀ k, x.coordinates.2.2 k = y.coordinates.2.2 k :=
      fun k => congrArg (fun w : Past p t => w.2.2.2 k) hw
    have hstate := physical_prechoice_eq_of_actual_past x y
      (ReferenceInitializationRun.run x s.val) h rfl rfl
      (fun j => congrArg (fun v => v.1 (nextBlock (ReferenceInitializationRun.run x s.val) h) j)
        hbase) (htarget _) t
      (fun u q hq => congrArg (fun w : Past p t => (w.1 ⟨q, hq⟩).1 u) hw)
      (fun q hq => congrArg (fun w : Past p t => (w.1 ⟨q, hq⟩).2) hw)
      (fun i q hq => congrArg
        (fun w : Past p t => w.2.2.1 ⟨⟨(i, q), (show q < t from hq).le⟩, hq⟩) hw)
    have hprofile : BootstrapPhysicalInput.currentBlockDrawProfile p
        (nextBlock (ReferenceInitializationRun.run x s.val) h)
        (ReferenceInitializationRun.run x s.val).numerators
        (ReferenceInitializationRun.run x s.val).weight_ge_one x.coordinates =
      BootstrapPhysicalInput.currentBlockDrawProfile p
        (nextBlock (ReferenceInitializationRun.run x s.val) h)
        (ReferenceInitializationRun.run x s.val).numerators
        (ReferenceInitializationRun.run x s.val).weight_ge_one y.coordinates := by
      unfold BootstrapPhysicalInput.currentBlockDrawProfile
      rw [hbase]
    have htargetArm := BootstrapPhysicalInput.targetArmMap_eq_of_target_scalar_eq p
      (nextBlock (ReferenceInitializationRun.run x s.val) h) x.coordinates y.coordinates (htarget _)
    exact congrArg some (Prod.ext rfl (Prod.ext hprofile (Prod.ext htargetArm hstate)))
  · rfl
  · rfl

/-- The accepted physical state map at a fixed boundary is measurable by
cases on its finite original draw values, followed by the accepted block map. -/
theorem measurable_physical_prechoice_at_fixedBoundary (b : Boundary p)
    (h : b.completed < n_boot p) :
    Measurable (fun e : Coordinates p => BootstrapPhysicalBlock.run
      (physical (input p ids rewards C_star C_h eta e) b h) t.val) := by
  let k := nextBlock b h
  let incoming := uninformed b
  let key := blockCaseKey p k incoming b.numerators b.weight_ge_one
  let branch := fun (c : IDArray p × BlockDrawCode p incoming) (z : InputCoordinates p) =>
    BootstrapBlockCausality.blockRun (s := k) incoming c.2.1 c.2.2.1
      c.2.2.2.1 c.1 c.2.2.2.2 rewards (localCoordinatesOf p incoming c.2 z) t.val
  have hkey : Measurable key := measurable_fst.prodMk
    (measurable_blockDrawCode p k incoming b.numerators b.weight_ge_one)
  have hbranch : ∀ c, Measurable (branch c) := by
    intro c
    exact (BootstrapBlockCausality.measurable_runInput (s := k) incoming c.2.1 c.2.2.1
      c.2.2.2.1 c.1 c.2.2.2.2 rewards t.val).comp
        (measurable_localCoordinatesOf p incoming c.2)
  have hm := (measurable_from_prod_countable_right
    (f := fun z : (IDArray p × BlockDrawCode p incoming) × InputCoordinates p =>
      branch z.1 z.2) hbranch).comp (hkey.prodMk measurable_id)
  exact hm.comp (measurable_const.prodMk measurable_id)

/-- All fields of a fixed-boundary descriptor are actual measurable maps. -/
theorem measurable_descriptorAtBoundary (b : Boundary p) :
    Measurable (fun e : Coordinates p =>
      descriptorAtBoundary p (input p ids rewards C_star C_h eta e) b t) := by
  unfold descriptorAtBoundary
  split_ifs with hc h
  · have hprofile : Measurable (fun e : Coordinates p =>
        BootstrapPhysicalInput.currentBlockDrawProfile p (nextBlock b h)
          b.numerators b.weight_ge_one e.2) :=
      (PrivateSourceStreams.measurable_blockDrawProfileMap p b.numerators b.weight_ge_one).comp
        ((measurable_pi_apply (nextBlock b h)).comp
          (measurable_fst.comp (measurable_fst.comp measurable_snd)))
    have htarget : Measurable (fun e : Coordinates p =>
        (physical (input p ids rewards C_star C_h eta e) b h).target) :=
      (BootstrapPhysicalInput.measurable_targetArmMap p (nextBlock b h)).comp measurable_snd
    exact (measurable_of_countable (some : Descriptor p → Option (Descriptor p))).comp
      (measurable_const.prodMk (hprofile.prodMk (htarget.prodMk
        (measurable_physical_prechoice_at_fixedBoundary ids rewards C_star C_h eta t b h))))
  · exact measurable_const
  · exact measurable_const

/-- Measurability of the descriptor of the actual generated stopped run. -/
theorem measurable_descriptor :
    Measurable (descriptor p ids rewards C_star C_h eta s t) := by
  have hb : Measurable (fun e : Coordinates p => ReferenceInitializationRun.run
      (input p ids rewards C_star C_h eta e) s.val) :=
    (measurable_run p C_star C_h eta rewards s.val).comp
      (measurable_const.prodMk measurable_id)
  exact (measurable_from_prod_countable_right
    (f := fun z : Boundary p × Coordinates p =>
      descriptorAtBoundary p (input p ids rewards C_star C_h eta z.2) z.1 t)
    (fun b => measurable_descriptorAtBoundary ids rewards C_star C_h eta t b)).comp
      (hb.prodMk measurable_id)

/-- A measurable past factor, evaluated through arbitrary fixed omitted
coordinates. The following reconstruction eliminates the completion. -/
def descriptorFromPast (e₀ : Coordinates p) (w : Past p t) : Option (Descriptor p) :=
  descriptor p ids rewards C_star C_h eta s t (complete p t e₀ w)

theorem measurable_descriptorFromPast (e₀ : Coordinates p) :
    Measurable (descriptorFromPast ids rewards C_star C_h eta s t e₀) :=
  (measurable_descriptor ids rewards C_star C_h eta s t).comp (measurable_complete p t e₀)

/-- Pointwise reconstruction for every original input, including opportunities
after launch. It uses no almost-everywhere exception or supplied history. -/
theorem descriptorFromPast_reconstruct (ht : t ∈ calendarBlock p s)
    (e₀ e : Coordinates p) :
    descriptorFromPast ids rewards C_star C_h eta s t e₀ (past p t e) =
      descriptor p ids rewards C_star C_h eta s t e := by
  apply descriptor_eq_of_past_eq ids rewards C_star C_h eta s t ht
  exact past_complete p t e₀ (past p t e)

/-- Every choice of omitted coordinates gives the same past factor, pointwise. -/
theorem descriptorFromPast_independent_of_completion (ht : t ∈ calendarBlock p s)
    (e₀ f₀ : Coordinates p) (w : Past p t) :
    descriptorFromPast ids rewards C_star C_h eta s t e₀ w =
      descriptorFromPast ids rewards C_star C_h eta s t f₀ w := by
  apply descriptor_eq_of_past_eq ids rewards C_star C_h eta s t ht
  rw [past_complete, past_complete]

/-- Original current-round public/private freshness against the actual generated
pre-choice descriptor, for every measurable event in the ENTIRE current vector.
The formula includes null/empty processed and boundary events without division. -/
theorem generated_cylinder (ht : t ∈ calendarBlock p s)
    (A : Set (Option (Descriptor p))) (hA : MeasurableSet A)
    (C : Set (Current p)) (hC : MeasurableSet C) :
    originalLaw p {e | descriptor p ids rewards C_star C_h eta s t e ∈ A ∧
      current p t e ∈ C} =
    originalLaw p {e | descriptor p ids rewards C_star C_h eta s t e ∈ A} *
      currentLaw p C := by
  obtain ⟨e₀⟩ := nonempty_of_isProbabilityMeasure (originalLaw p)
  let F := descriptorFromPast ids rewards C_star C_h eta s t e₀
  have hF := measurable_descriptorFromPast ids rewards C_star C_h eta s t e₀
  have hrec : ∀ e, F (past p t e) = descriptor p ids rewards C_star C_h eta s t e :=
    descriptorFromPast_reconstruct ids rewards C_star C_h eta s t ht e₀
  have hjoint := (past_current_measurePreserving p t).measure_preimage
    ((hF hA).prod hC).nullMeasurableSet
  have hpast := (measurePreserving_fst (μ := pastLaw p t) (ν := currentLaw p)).comp
    (past_current_measurePreserving p t)
  have hmarginal := hpast.measure_preimage (hF hA).nullMeasurableSet
  have hevent : (fun e => (past p t e, current p t e)) ⁻¹' ((F ⁻¹' A) ×ˢ C) =
      {e | descriptor p ids rewards C_star C_h eta s t e ∈ A ∧ current p t e ∈ C} := by
    ext e
    simp only [Set.mem_preimage, Set.mem_prod, hrec, Set.mem_ofPred_eq]
  have hmarg : (fun e : Coordinates p => past p t e) ⁻¹' (F ⁻¹' A) =
      {e | descriptor p ids rewards C_star C_h eta s t e ∈ A} := by
    ext e
    simp only [Set.mem_preimage, hrec, Set.mem_ofPred_eq]
  rw [hevent, Measure.prod_prod] at hjoint
  change originalLaw p ((fun e => past p t e) ⁻¹' (F ⁻¹' A)) =
    pastLaw p t (F ⁻¹' A) at hmarginal
  rw [hmarg] at hmarginal
  exact hjoint.trans (congrArg (fun a => a * currentLaw p C) hmarginal.symm)

/-- The atom event refers to the original generated boundary and the actual
no-crossing/remaining-block guards, with no supplied equal-state premise. -/
theorem descriptor_eq_some_iff (e : Coordinates p) (b : Boundary p)
    (d : PrivateSourceStreams.BlockDrawProfile p) (a : Fin p.K)
    (st : BootstrapPhysicalBlock.State p) :
    descriptor p ids rewards C_star C_h eta s t e = some (b, (d, (a, st))) ↔
      let x := input p ids rewards C_star C_h eta e
      let c := ReferenceInitializationRun.run x s.val
      c = b ∧ c.crossing = none ∧ ∃ h : c.completed < n_boot p,
        BootstrapPhysicalInput.currentBlockDrawProfile p (nextBlock c h)
          c.numerators c.weight_ge_one x.coordinates = d ∧
        (physical x c h).target = a ∧ BootstrapPhysicalBlock.run (physical x c h) t.val = st :=
  descriptorAtBoundary_eq_some_iff p (input p ids rewards C_star C_h eta e)
    (ReferenceInitializationRun.run (input p ids rewards C_star C_h eta e) s.val) b t d a st

/-- Actual processed boundary/profile/target/pre-choice-state atom law. Full
profile entries outside the incoming set remain labelled latent draws. -/
theorem generated_processed_atom (ht : t ∈ calendarBlock p s)
    (b : Boundary p) (d : PrivateSourceStreams.BlockDrawProfile p)
    (a : Fin p.K) (st : BootstrapPhysicalBlock.State p)
    (C : Set (Current p)) (hC : MeasurableSet C) :
    originalLaw p {e | descriptor p ids rewards C_star C_h eta s t e =
        some (b, (d, (a, st))) ∧ current p t e ∈ C} =
    originalLaw p {e | descriptor p ids rewards C_star C_h eta s t e =
      some (b, (d, (a, st)))} * currentLaw p C := by
  exact generated_cylinder ids rewards C_star C_h eta s t ht
    {some (b, (d, (a, st)))} (measurableSet_singleton _) C hC

/-- The same generated atom law written with the original producer and
physical fields. The existential is only the remaining-block proof, with
all data determined by the original input, including the no-crossing guard. -/
theorem generated_physical_atom (ht : t ∈ calendarBlock p s)
    (b : Boundary p) (d : PrivateSourceStreams.BlockDrawProfile p)
    (a : Fin p.K) (st : BootstrapPhysicalBlock.State p)
    (C : Set (Current p)) (hC : MeasurableSet C) :
    originalLaw p {e |
      (let x := input p ids rewards C_star C_h eta e
       let c := ReferenceInitializationRun.run x s.val
       c = b ∧ c.crossing = none ∧ ∃ h : c.completed < n_boot p,
         BootstrapPhysicalInput.currentBlockDrawProfile p (nextBlock c h)
           c.numerators c.weight_ge_one x.coordinates = d ∧
         (physical x c h).target = a ∧
         BootstrapPhysicalBlock.run (physical x c h) t.val = st) ∧ current p t e ∈ C} =
    originalLaw p {e |
      let x := input p ids rewards C_star C_h eta e
      let c := ReferenceInitializationRun.run x s.val
      c = b ∧ c.crossing = none ∧ ∃ h : c.completed < n_boot p,
        BootstrapPhysicalInput.currentBlockDrawProfile p (nextBlock c h)
          c.numerators c.weight_ge_one x.coordinates = d ∧
        (physical x c h).target = a ∧
        BootstrapPhysicalBlock.run (physical x c h) t.val = st} * currentLaw p C := by
  simpa only [descriptor_eq_some_iff] using
    generated_processed_atom ids rewards C_star C_h eta s t ht b d a st C hC

end Generated

end Bandits.Support.GeneratedBootstrapRoundLaw

end
