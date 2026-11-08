/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
public import Bandits.Support.GeneratedBootstrapGainBudget
public import Bandits.Support.GeneratedProductiveExitBudget
public import Bandits.Support.PrivateSourceStreams
public import Bandits.Support.ReferenceInitializationMeasurability

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Auxiliary raw-coordinate held-arm reveal filtration

Sources motivating the indexing and indicators:
`sources/zip4/manuscript/appendix_b_communication.tex:376-381,520-532,586-625`
and `sources/zip4/manuscript/07_public_setup.tex:63-113`.

This is an enlarged auxiliary analysis filtration on the same original full
coordinate carrier and `GeneratedBootstrapRoundLaw.originalLaw`.  Its base is
`GeneratedBootstrapBlockFiltrationRepair.boundarySigma`: all earlier raw
follower triples and target scalars remain in that base, including private-ID
scalars on inactive blocks and unused target scalars after coordinator launch.
It also retains the earlier calendar and player/round coordinates of the raw
prefix.  This base is not identified with the manuscript's `F_s`.

At each genuine zero-based block index the current join adds only this
follower's actual latent (activity, held arm) pair, read from the run's incoming
numerators and its existing labelled follower/block triple.  It adds no current
private-ID scalar, current coordinator target scalar, current calendar controls,
future coordinates, or remaining row coordinates.  The unused past coordinates
already in the raw base are retained.  Latent pairs are still read after the
analysis indicator/update stops; physical execution continues.  No new random
draws, second run, changed protocol, or extra information supplied to physical
players is introduced.

The module proves auxiliary filtration inclusions, indicator adaptedness,
boundedness, integrability, and a deterministic one-exit count.  Zero-based
index `s` corresponds to manuscript block `s+1` only as an indexing alignment.
Neither `revealSigma` nor `heldArmRevealFiltration`, including its terminal raw
boundary, is asserted equal to the manuscript's `K_s` or `H_s` (or `F_s`).
Measurability for this enlargement does not establish adaptedness or a
conditional bound for the manuscript's smaller history.

No actual conditional-success or activity law, conditional freshness, success
probability, or stochastic tail bound is proved here.  A future argument using
this enlargement must prove the needed conditional law for this same enlarged
sigma algebra.  No source-facing declaration is approved or frozen here, and
no manuscript lemma or regret theorem is closed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CompletePublicTable
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.ReferencePrelaunchFollower
open scoped Classical

namespace Bandits.Support.GeneratedHeldArmRevealFiltration

abbrev Parameters := ConstructorDimensions.Parameters

private theorem measurable_of_countable_left {α β γ : Type*}
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSpace γ]
    (f : α × β → γ) (hf : ∀ a, Measurable (fun b => f (a, b))) : Measurable f := by
  intro t ht
  have hpre : f ⁻¹' t = ⋃ a : α, ({a} : Set α) ×ˢ ((fun b => f (a, b)) ⁻¹' t) := by
    ext z
    rcases z with ⟨a, b⟩
    simp
  rw [hpre]
  exact MeasurableSet.iUnion fun a =>
    MeasurableSet.prod (measurableSet_singleton a) (hf a ht)

/-- The only observation added to the raw base at opportunity `s`: this
follower's original latent activity bit and held arm.  The current triple's
third, private-ID component is omitted from this pair; past raw private-ID
coordinates remain in the base. -/
def revealedPair (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p))
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) : Bool × Fin p.K :=
  let x_e := GeneratedBootstrapBlockFiltrationRepair.referenceInput
    p ids rewards C_star C_h eta e
  let d := GeneratedBootstrapGainBudget.latentBlockProfileAt x_e i s
  (d.1, d.2.1)

/-- A section of the observed pair through the raw-coordinate `SourcePrefix`
ending at the right boundary of block `s`.  This accepted prefix carrier is an
auxiliary enlargement, not a manuscript history.  Completion fills omitted
coordinates from a fixed original point only to define this measurable
section. -/
def revealFromSourcePrefix (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (e₀ : GeneratedBootstrapBlockFiltrationRepair.Coordinates p)
    (a : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p (s.val + 1)) :
    Bool × Fin p.K :=
  let x_e := GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards
    C_star C_h eta
    (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p (s.val + 1) e₀ a)
  let d := GeneratedBootstrapGainBudget.latentBlockProfileAt x_e i s
  (d.1, d.2.1)

/-- The observed pair factors through the raw-coordinate prefix using the
actual block-`s` triple and the run numerators at raw boundary `s`. -/
theorem revealedPair_eq_revealFromSourcePrefix (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (e₀ e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    revealedPair p ids rewards C_star C_h eta i s e =
      revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀
        (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1) e) := by
  let r := s.val + 1
  let completed := GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p r e₀
    (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p r e)
  have hsrc := GeneratedBootstrapBlockFiltrationRepair.sourcePrefix_completeSourcePrefix
    p r e₀ (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p r e)
  have hprev : GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val completed =
      GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p s.val e := by
    have hrestrict := congrArg
      (GeneratedBootstrapBlockFiltrationRepair.sourcePrefixRestrict p s.val r (Nat.le_succ _))
      hsrc
    simpa only [GeneratedBootstrapBlockFiltrationRepair.sourcePrefixRestrict_sourcePrefix]
      using hrestrict
  have hrun := GeneratedBootstrapBlockFiltrationRepair.run_eq_of_sourcePrefix_eq
    p s.val ids rewards C_star C_h eta completed e hprev
  have hblocks : completed.2.1.1 s = e.2.1.1 s := by
    have hblockPrefix := congrArg
      (fun z : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p r => z.2.1) hsrc
    exact congrFun hblockPrefix ⟨s, Nat.lt_succ_self s.val⟩
  let completedInput := GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards
    C_star C_h eta completed
  let originalInput := GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards
    C_star C_h eta e
  change
    (let d := GeneratedBootstrapGainBudget.latentBlockProfileAt
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e) i s;
      (d.1, d.2.1)) =
    (let d := GeneratedBootstrapGainBudget.latentBlockProfileAt
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta
        (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p r e₀
          (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p r e))) i s;
      (d.1, d.2.1))
  simp only [GeneratedBootstrapGainBudget.latentBlockProfileAt,
    GeneratedBootstrapGainBudget.boundaryAt]
  have hscalar :
      completedInput.coordinates.1.1 s = originalInput.coordinates.1.1 s := by
    change completed.2.1.1 s = e.2.1.1 s
    exact hblocks
  have hprofile :
      PrivateSourceStreams.blockDrawProfileMap p
        (ReferenceInitializationRun.run
          completedInput s.val).numerators
        (ReferenceInitializationRun.run
          completedInput s.val).weight_ge_one
        (completedInput.coordinates.1.1 s)
        (BootstrapPhysicalInput.sourceFollowerIndex p i) =
      PrivateSourceStreams.blockDrawProfileMap p
        (ReferenceInitializationRun.run
          originalInput s.val).numerators
        (ReferenceInitializationRun.run
          originalInput s.val).weight_ge_one
        (originalInput.coordinates.1.1 s)
        (BootstrapPhysicalInput.sourceFollowerIndex p i) := by
    calc
      _ = PrivateSourceStreams.blockDrawProfileMap p
          (ReferenceInitializationRun.run originalInput s.val).numerators
          (ReferenceInitializationRun.run originalInput s.val).weight_ge_one
          (completedInput.coordinates.1.1 s)
          (BootstrapPhysicalInput.sourceFollowerIndex p i) :=
        congrArg (fun b : ReferenceInitializationRun.Boundary p =>
          PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one
            (completedInput.coordinates.1.1 s)
            (BootstrapPhysicalInput.sourceFollowerIndex p i)) hrun
      _ = _ := congrArg (fun v : Fin (p.m - 1) → PrivateSourceStreams.BlockScalars =>
        PrivateSourceStreams.blockDrawProfileMap p
          (ReferenceInitializationRun.run originalInput s.val).numerators
          (ReferenceInitializationRun.run originalInput s.val).weight_ge_one v
          (BootstrapPhysicalInput.sourceFollowerIndex p i)) hscalar
  rw [hprofile]

/-- Measurability of the raw-prefix section.  Its inputs are the accepted
incoming run boundary and the existing block-`s` scalar profile. -/
theorem measurable_revealFromSourcePrefix (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (e₀ : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    Measurable (revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀) := by
  let r := s.val + 1
  let complete := GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p r e₀
  have hcomplete : Measurable complete :=
    GeneratedBootstrapBlockFiltrationRepair.measurable_completeSourcePrefix p r e₀
  have hrunAmbient : Measurable (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
      ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
        s.val) := by
    exact (GeneratedBootstrapBlockFiltrationRepair.measurable_run p s.val ids rewards
      C_star C_h eta).mono
        (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration_le_ambient p s.val) le_rfl
  have hstate : Measurable (fun a : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p r =>
      ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta
          (complete a)) s.val) := hrunAmbient.comp hcomplete
  have hscalarProfile : Measurable
      (fun a : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p r =>
        (complete a).2.1.1 s) := by
    have hrepr : (fun a : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p r =>
        (complete a).2.1.1 s) =
          fun a => a.2.1 ⟨s, Nat.lt_succ_self s.val⟩ := by
      funext a
      simp [complete, r, GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix]
    rw [hrepr]
    fun_prop
  have hdata : Measurable (fun a : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p r =>
      (ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta
          (complete a)) s.val,
        (complete a).2.1.1 s)) := hstate.prodMk hscalarProfile
  have hdraw : Measurable
      (fun z : ReferenceInitializationRun.Boundary p ×
          (Fin (p.m - 1) → PrivateSourceStreams.BlockScalars) =>
        let d := PrivateSourceStreams.blockDrawProfileMap p z.1.numerators
          z.1.weight_ge_one z.2 (BootstrapPhysicalInput.sourceFollowerIndex p i)
        (d.1, d.2.1)) := by
    apply measurable_of_countable_left
    intro b
    have hprofile := PrivateSourceStreams.measurable_blockDrawProfileMap p
      b.numerators b.weight_ge_one
    have hdrawAt := (measurable_pi_apply
      (BootstrapPhysicalInput.sourceFollowerIndex p i)).comp hprofile
    exact (measurable_fst.comp hdrawAt).prodMk
      (measurable_fst.comp (measurable_snd.comp hdrawAt))
  have hrepr :
      (fun a : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p r =>
        revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀ a) =
      (fun a =>
        let d := PrivateSourceStreams.blockDrawProfileMap p
          (ReferenceInitializationRun.run
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta
              (complete a)) s.val).numerators
          (ReferenceInitializationRun.run
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta
              (complete a)) s.val).weight_ge_one
          ((complete a).2.1.1 s) (BootstrapPhysicalInput.sourceFollowerIndex p i)
        (d.1, d.2.1)) := by
    funext a
    rfl
  change Measurable (fun a => revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀ a)
  rw [hrepr]
  exact hdraw.comp hdata

/-- The observed pair is measurable on the original ambient coordinate
carrier. -/
theorem measurable_revealedPair (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    Measurable (revealedPair p ids rewards C_star C_h eta i s) := by
  let e₀ : GeneratedBootstrapBlockFiltrationRepair.Coordinates p :=
    Classical.choice (nonempty_of_isProbabilityMeasure
      (GeneratedBootstrapRoundLaw.originalLaw p))
  have hfactor : (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
      revealedPair p ids rewards C_star C_h eta i s e) =
      (revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀ ∘
        GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1)) := by
    funext e
    exact revealedPair_eq_revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀ e
  change Measurable (fun e => revealedPair p ids rewards C_star C_h eta i s e)
  rw [hfactor]
  exact (measurable_revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀).comp
    (GeneratedBootstrapBlockFiltrationRepair.measurable_sourcePrefix p (s.val + 1))

/-- The same latent pair is measurable at the next raw boundary, including
after analytical stopping.  Physical execution continues. -/
theorem measurable_revealedPair_at_nextBoundary (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) (Bool × Fin p.K)
      (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (s.val + 1)) inferInstance
      (revealedPair p ids rewards C_star C_h eta i s) := by
  let e₀ : GeneratedBootstrapBlockFiltrationRepair.Coordinates p :=
    Classical.choice (nonempty_of_isProbabilityMeasure
      (GeneratedBootstrapRoundLaw.originalLaw p))
  have hprefix :
      @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p)
        (GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p (s.val + 1))
        (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (s.val + 1)) inferInstance
        (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1)) :=
    comap_measurable _
  have hsection :=
    (measurable_revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀).comp hprefix
  have hfactor : (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
      revealedPair p ids rewards C_star C_h eta i s e) =
      (revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀ ∘
        GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1)) := by
    funext e
    exact revealedPair_eq_revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀ e
  change @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) (Bool × Fin p.K)
    (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (s.val + 1)) inferInstance
    (fun e => revealedPair p ids rewards C_star C_h eta i s e)
  rw [hfactor]
  exact hsection

/-- Auxiliary block sigma algebra: the enlarged incoming raw boundary joined
with only this follower's current latent activity/held-arm pair.  The base
retains all earlier raw triples and targets, including unused private-ID
scalars on inactive blocks and unused targets after launch.  The join adds no
current private ID, target, or future coordinates.  No equality with manuscript
`K_s` or conditional-success/activity law is asserted. -/
@[instance_reducible] def revealSigma (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) : MeasurableSpace (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :=
  GeneratedBootstrapBlockFiltrationRepair.boundarySigma p s.val ⊔
    MeasurableSpace.comap (revealedPair p ids rewards C_star C_h eta i s) inferInstance

theorem boundarySigma_le_revealSigma (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    GeneratedBootstrapBlockFiltrationRepair.boundarySigma p s.val ≤
      revealSigma p ids rewards C_star C_h eta i s := le_sup_left

theorem measurable_revealedPair_at_revealSigma (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) (Bool × Fin p.K)
      (revealSigma p ids rewards C_star C_h eta i s) inferInstance
      (revealedPair p ids rewards C_star C_h eta i s) := by
  exact (comap_measurable (revealedPair p ids rewards C_star C_h eta i s)).mono
    le_sup_right le_rfl

theorem revealSigma_le_nextBoundary (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    revealSigma p ids rewards C_star C_h eta i s ≤
      GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (s.val + 1) := by
  let e₀ : GeneratedBootstrapBlockFiltrationRepair.Coordinates p :=
    Classical.choice (nonempty_of_isProbabilityMeasure
      (GeneratedBootstrapRoundLaw.originalLaw p))
  have hfactor :
      (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
        revealedPair p ids rewards C_star C_h eta i s e) =
      (revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀ ∘
        GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1)) := by
    funext e
    exact revealedPair_eq_revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀ e
  have hcomap := MeasurableSpace.comap_le_comap_of_eq_comp
    (revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀)
    (measurable_revealFromSourcePrefix p ids rewards C_star C_h eta i s e₀) hfactor
  unfold revealSigma
  exact sup_le
    ((GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p).mono'
      (Nat.le_succ s.val)) hcomap

theorem revealSigma_le_revealSigma_succ (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (hs : s.val + 1 < n_boot p) :
    revealSigma p ids rewards C_star C_h eta i s ≤
      revealSigma p ids rewards C_star C_h eta i ⟨s.val + 1, hs⟩ := by
  exact (revealSigma_le_nextBoundary p ids rewards C_star C_h eta i s).trans le_sup_left

/-- The updater's enabled bit is the latent activity bit exactly when the
incoming boundary is prelaunch and the follower is still uninformed. -/
theorem blockAt_enabled_eq_revealedActivity (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    (GeneratedBootstrapGainBudget.blockAt
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
      i s).enabled =
        if (ReferenceInitializationRun.run
              (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
              s.val).crossing = none ∧
            (ReferenceInitializationRun.run
              (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
              s.val).activation i = none
        then (revealedPair p ids rewards C_star C_h eta i s e).1 else false := by
  let x := GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e
  let b := ReferenceInitializationRun.run x s.val
  change (GeneratedBootstrapPotential.actualBlock x i s).enabled = _
  by_cases hc : b.crossing = none
  · by_cases hi : i ∈ ReferenceInitializationRun.uninformed b
    · have hcompleted := GeneratedBootstrapPotential.completed_eq_of_no_crossing x s.val
        s.isLt.le hc
      have hnext : ReferenceInitializationRun.nextBlock b
          (by rw [hcompleted]; exact s.isLt) = s := Fin.ext hcompleted
      have hactual := GeneratedBootstrapPotential.actualBlock_eq_weightInput x i s hc hi
      have hfields := ReferenceInitializationMeasurability.weightInput_fields x b
        (by rw [hcompleted]; exact s.isLt) ⟨i, hi⟩
      have hdraw := ReferenceInitializationRun.physical_own_block_draw x b
        (by rw [hcompleted]; exact s.isLt) ⟨i, hi⟩
      have hactive : (ReferenceInitializationRun.physical x b
          (by rw [hcompleted]; exact s.isLt)).active ⟨i, hi⟩ =
          (PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one
            (x.coordinates.1.1 (ReferenceInitializationRun.nextBlock b
              (by rw [hcompleted]; exact s.isLt)))
            (BootstrapPhysicalInput.sourceFollowerIndex p i)).1 :=
        congrArg (fun d : PrivateSourceStreams.BlockDraw p => d.1) hdraw
      have hactive' : (ReferenceInitializationRun.physical x b
          (by rw [hcompleted]; exact s.isLt)).active ⟨i, hi⟩ =
          (GeneratedBootstrapGainBudget.latentBlockProfileAt x i s).1 := by
        calc
          _ = (PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one
              (x.coordinates.1.1 (ReferenceInitializationRun.nextBlock b
                (by rw [hcompleted]; exact s.isLt)))
              (BootstrapPhysicalInput.sourceFollowerIndex p i)).1 := hactive
          _ = (PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one
              (x.coordinates.1.1 s)
              (BootstrapPhysicalInput.sourceFollowerIndex p i)).1 := by
            exact congrArg Prod.fst (congrArg
              (fun q : Fin (n_boot p) =>
                PrivateSourceStreams.blockDrawProfileMap p b.numerators b.weight_ge_one
                  (x.coordinates.1.1 q) (BootstrapPhysicalInput.sourceFollowerIndex p i)) hnext)
          _ = (GeneratedBootstrapGainBudget.latentBlockProfileAt x i s).1 := rfl
      calc
        (GeneratedBootstrapPotential.actualBlock x i s).enabled =
            (ReferenceInitializationRun.weightInput x b
              (by rw [hcompleted]; exact s.isLt) ⟨i, hi⟩).enabled :=
          congrArg BootstrapWeightPotential.Block.enabled hactual
        _ = (ReferenceInitializationRun.physical x b
              (by rw [hcompleted]; exact s.isLt)).active ⟨i, hi⟩ := hfields.1
        _ = (GeneratedBootstrapGainBudget.latentBlockProfileAt x i s).1 := hactive'
        _ = if b.crossing = none ∧ b.activation i = none then
              (revealedPair p ids rewards C_star C_h eta i s e).1 else false := by
          have hnone : b.activation i = none :=
            (ReferenceInitializationRun.mem_uninformed b i).mp hi
          simp [revealedPair, GeneratedBootstrapGainBudget.latentBlockProfileAt,
            GeneratedBootstrapGainBudget.boundaryAt, x, b, hc, hnone]
    · have hactivation : b.activation i ≠ none := by
        intro hnone
        exact hi ((ReferenceInitializationRun.mem_uninformed b i).mpr hnone)
      have hdisabled := GeneratedBootstrapPotential.actualBlock_disabled_of_activated
        x i s hactivation
      rw [hdisabled]
      simp [x, b, hc, hactivation]
  · have hdisabled : (GeneratedBootstrapPotential.actualBlock x i s).enabled = false := by
      simp [GeneratedBootstrapPotential.actualBlock, b, hc]
    rw [hdisabled]
    simp [x, b, hc]

/-- The updater's stored arm is the same original latent held arm, including
on inactive, informed, and postlaunch analysis blocks. -/
theorem blockAt_held_eq_revealedHeld (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    (GeneratedBootstrapGainBudget.blockAt
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
      i s).held = (revealedPair p ids rewards C_star C_h eta i s e).2 := by
  change (GeneratedBootstrapPotential.actualBlock
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
      i s).held = _
  rw [GeneratedBootstrapPotential.actualBlock_held_eq_actualLatentHeldArm]
  rfl

/-- Monotonicity of finite reveal sigma algebras at arbitrary in-horizon
indices. -/
theorem revealSigma_le_of_le (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (r q : ℕ) (hr : r < n_boot p) (hq : q < n_boot p) (hrq : r ≤ q) :
    revealSigma p ids rewards C_star C_h eta i ⟨r, hr⟩ ≤
      revealSigma p ids rewards C_star C_h eta i ⟨q, hq⟩ := by
  by_cases heq : r = q
  · subst q
    exact le_rfl
  · have hrq' : r < q := lt_of_le_of_ne hrq heq
    calc
      revealSigma p ids rewards C_star C_h eta i ⟨r, hr⟩ ≤
          GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (r + 1) :=
        revealSigma_le_nextBoundary p ids rewards C_star C_h eta i ⟨r, hr⟩
      _ ≤ GeneratedBootstrapBlockFiltrationRepair.boundarySigma p q :=
        (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p).mono'
          (Nat.succ_le_of_lt hrq')
      _ ≤ revealSigma p ids rewards C_star C_h eta i ⟨q, hq⟩ := le_sup_left

/-- Nat-indexed auxiliary raw-coordinate filtration.  At zero-based index `r`
below the horizon it uses `revealSigma` for block `r`; this only aligns indices
with manuscript block `r+1`.  From the horizon onward it is held constant at
`boundarySigma p (n_boot p)`, retaining unused past private-ID and target
coordinates.  This terminal raw boundary is not identified with manuscript
`F_n`, and this filtration is not identified with manuscript `H_s`. -/
def heldArmRevealFiltration (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m) :
    Filtration ℕ (inferInstance : MeasurableSpace
      (GeneratedBootstrapBlockFiltrationRepair.Coordinates p)) where
  seq r := if h : r < n_boot p then revealSigma p ids rewards C_star C_h eta i ⟨r, h⟩
    else GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (n_boot p)
  mono' := by
    intro r q hrq
    by_cases hr : r < n_boot p
    · by_cases hq : q < n_boot p
      · simp only [dite_eq_left hr, dite_eq_left hq]
        exact revealSigma_le_of_le p ids rewards C_star C_h eta i r q hr hq hrq
      · simp only [dite_eq_left hr, dite_eq_right hq]
        calc
          revealSigma p ids rewards C_star C_h eta i ⟨r, hr⟩ ≤
              GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (r + 1) :=
            revealSigma_le_nextBoundary p ids rewards C_star C_h eta i ⟨r, hr⟩
          _ ≤ GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (n_boot p) :=
            (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p).mono'
              (Nat.succ_le_of_lt hr)
    · have hrn : n_boot p ≤ r := Nat.le_of_not_gt hr
      have hqn : n_boot p ≤ q := hrn.trans hrq
      have hq : ¬ q < n_boot p := Nat.not_lt_of_ge hqn
      simp only [dite_eq_right hr, dite_eq_right hq]
      exact le_rfl
  le' := by
    intro r
    by_cases hr : r < n_boot p
    · simp only [dite_eq_left hr]
      exact (revealSigma_le_nextBoundary p ids rewards C_star C_h eta i ⟨r, hr⟩).trans
        (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration_le_ambient p (r + 1))
    · simp only [dite_eq_right hr]
      exact GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration_le_ambient p (n_boot p)

theorem heldArmRevealFiltration_at_block (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    heldArmRevealFiltration p ids rewards C_star C_h eta i s.val =
      revealSigma p ids rewards C_star C_h eta i s := by
  simp [heldArmRevealFiltration, s.isLt]

/-- The auxiliary filtration at its horizon is the terminal raw boundary,
including unused past coordinates; this is no manuscript-history identity. -/
theorem heldArmRevealFiltration_at_horizon (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m) :
    heldArmRevealFiltration p ids rewards C_star C_h eta i (n_boot p) =
      GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (n_boot p) := by
  simp [heldArmRevealFiltration]

/-- The auxiliary filtration retains that same enlarged terminal raw boundary
at every index beyond the finite horizon. -/
theorem heldArmRevealFiltration_eq_terminal_of_ge (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m) (r : ℕ)
    (hr : n_boot p ≤ r) :
    heldArmRevealFiltration p ids rewards C_star C_h eta i r =
      GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (n_boot p) := by
  simp [heldArmRevealFiltration, Nat.not_lt_of_ge hr]

/-- The next raw boundary embeds into the auxiliary filtration at `s+1`.
For the final genuine block this is equality with its terminal raw boundary;
no identity with manuscript `H_n` or `F_n` is asserted. -/
theorem nextBoundary_le_heldArmRevealFiltration_succ (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (s.val + 1) ≤
      heldArmRevealFiltration p ids rewards C_star C_h eta i (s.val + 1) := by
  by_cases hs : s.val + 1 < n_boot p
  · rw [heldArmRevealFiltration_at_block p ids rewards C_star C_h eta i
      ⟨s.val + 1, hs⟩]
    exact le_sup_left
  · have hlast : s.val + 1 = n_boot p := by omega
    rw [hlast, heldArmRevealFiltration_at_horizon]

/-- The productive indicator is measurable for the enlarged auxiliary
`revealSigma`, through its literal enabled gate and original latent held arm.
This proves neither adaptedness to manuscript `K_s` nor any conditional bound. -/
theorem measurable_productiveIndicator (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) ℝ
      (revealSigma p ids rewards C_star C_h eta i s) inferInstance
      (fun e => GeneratedBootstrapGainBudget.productiveIndicator
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
        i s) := by
  let _ : MeasurableSpace (ReferenceInitializationRun.Boundary p) :=
    ReferenceInitializationMeasurability.boundaryMeasurableSpace p
  have hspace := boundarySigma_le_revealSigma p ids rewards C_star C_h eta i s
  have hrun := GeneratedBootstrapBlockFiltrationRepair.measurable_run p s.val ids rewards
    C_star C_h eta
  have hrun' := hrun.mono hspace le_rfl
  have hcross : @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p)
      (Option (Fin (n_boot p)))
      (revealSigma p ids rewards C_star C_h eta i s) inferInstance
      (fun e => (ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
        s.val).crossing) :=
    (measurable_of_countable
      (fun b : ReferenceInitializationRun.Boundary p => b.crossing)).comp hrun'
  have hactivation : @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p)
      (Option (ReferencePrelaunchFollower.Activation p))
      (revealSigma p ids rewards C_star C_h eta i s) inferInstance
      (fun e =>
        (ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
          s.val).activation i) :=
    (measurable_of_countable
      (fun b : ReferenceInitializationRun.Boundary p => b.activation i)).comp hrun'
  have hpair := measurable_revealedPair_at_revealSigma p ids rewards C_star C_h eta i s
  have hdata := (hcross.prodMk hactivation).prodMk hpair
  have hcalc : Measurable
      (fun z : (Option (Fin (n_boot p)) × Option (ReferencePrelaunchFollower.Activation p)) ×
          (Bool × Fin p.K) =>
        if (if z.1.1 = none ∧ z.1.2 = none then z.2.1 else false) = true ∧
            (BootstrapStartupCostScale.h_boot C_h p : ℝ) ≤
              BootstrapDownCountMean.rewardSupportCount p s rewards z.2.2
        then (1 : ℝ) else 0) := measurable_of_countable _
  have hrepr :
      (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
        GeneratedBootstrapGainBudget.productiveIndicator
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
          i s) =
      ((fun z : (Option (Fin (n_boot p)) ×
          Option (ReferencePrelaunchFollower.Activation p)) × (Bool × Fin p.K) =>
        if (if z.1.1 = none ∧ z.1.2 = none then z.2.1 else false) = true ∧
            (BootstrapStartupCostScale.h_boot C_h p : ℝ) ≤
              BootstrapDownCountMean.rewardSupportCount p s rewards z.2.2
        then (1 : ℝ) else 0) ∘
        (fun e => (((ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
          s.val).crossing,
          (ReferenceInitializationRun.run
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
            s.val).activation i),
          revealedPair p ids rewards C_star C_h eta i s e))) := by
    funext e
    rw [GeneratedBootstrapGainBudget.productiveIndicator,
      blockAt_enabled_eq_revealedActivity p ids rewards C_star C_h eta i s e,
      blockAt_held_eq_revealedHeld p ids rewards C_star C_h eta i s e]
    simp only [GeneratedBootstrapBlockFiltrationRepair.referenceInput,
      GeneratedBootstrapRoundLaw.input,
      ReferenceInitializationMeasurability.inputOfCoordinates]
    by_cases hc : (ReferenceInitializationRun.run
        { ids := ids, row := e.1, rewards := rewards, coordinates := e.2,
          C_star := C_star, C_h := C_h, eta := eta } s.val).crossing = none
    · by_cases ha : (ReferenceInitializationRun.run
          { ids := ids, row := e.1, rewards := rewards, coordinates := e.2,
            C_star := C_star, C_h := C_h, eta := eta } s.val).activation i = none
      · simp [hc, ha, GeneratedBootstrapGainBudget.startupThreshold,
          GeneratedBootstrapGainBudget.rewardSupportCountAt]
      · simp [hc, ha, GeneratedBootstrapGainBudget.startupThreshold,
          GeneratedBootstrapGainBudget.rewardSupportCountAt]
    · simp [hc, GeneratedBootstrapGainBudget.startupThreshold,
        GeneratedBootstrapGainBudget.rewardSupportCountAt]
  rw [hrepr]
  exact hcalc.comp hdata

/-- The productive indicator at zero-based block `s` is adapted to the
auxiliary history at index `s`.  Its correspondence with manuscript block
`s+1` is an indexing alignment only, with no equality of histories. -/
theorem measurable_productiveIndicator_at_auxiliaryHistory (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) ℝ
      (heldArmRevealFiltration p ids rewards C_star C_h eta i s.val) inferInstance
      (fun e => GeneratedBootstrapGainBudget.productiveIndicator
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
        i s) := by
  exact (measurable_productiveIndicator p ids rewards C_star C_h eta i s).mono
    (le_of_eq (heldArmRevealFiltration_at_block p ids rewards C_star C_h eta i s).symm) le_rfl

/-- The original latent activity indicator is measurable at the next raw
boundary, including after analytical stopping while physical execution
continues.  No conditional activity law is asserted. -/
theorem measurable_latentActivityIndicator_at_nextBoundary (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) ℝ
      (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (s.val + 1)) inferInstance
      (fun e => GeneratedBootstrapGainBudget.latentActivityIndicator
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
        i s) := by
  have hpair := measurable_revealedPair_at_nextBoundary p ids rewards C_star C_h eta i s
  have hmap : Measurable (fun z : Bool × Fin p.K => if z.1 then (1 : ℝ) else 0) :=
    measurable_of_countable _
  have hrepr :
      (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
        GeneratedBootstrapGainBudget.latentActivityIndicator
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
          i s) =
      (fun e => if (revealedPair p ids rewards C_star C_h eta i s e).1 then (1 : ℝ) else 0) := by
    funext e
    rfl
  rw [hrepr]
  exact hmap.comp hpair

/-- The accepted productive indicator is measurable at the next raw
boundary, by promotion from the enlarged auxiliary `revealSigma`. -/
theorem measurable_productiveIndicator_at_nextBoundary (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) ℝ
      (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (s.val + 1)) inferInstance
      (fun e => GeneratedBootstrapGainBudget.productiveIndicator
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
        i s) := by
  exact (measurable_productiveIndicator p ids rewards C_star C_h eta i s).mono
    (revealSigma_le_nextBoundary p ids rewards C_star C_h eta i s) le_rfl

/-- The auxiliary history at zero-based block index `s` is its `revealSigma`.
The index corresponds to manuscript block `s+1` only as an indexing alignment;
this equality is solely between the two auxiliary constructions. -/
theorem auxiliaryBlockIndex_history_eq_revealSigma (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    heldArmRevealFiltration p ids rewards C_star C_h eta i s.val =
      revealSigma p ids rewards C_star C_h eta i s :=
  heldArmRevealFiltration_at_block p ids rewards C_star C_h eta i s

/-- The actual productive exit indicator is measurable at the next raw
boundary; its factors are the accepted productive indicator and the accepted
prelaunch/uninformed indicator. -/
theorem measurable_productiveExitIndicator_at_nextBoundary (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) ℝ
      (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (s.val + 1)) inferInstance
      (fun e => GeneratedProductiveExitBudget.productiveExitIndicator
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
        i s) := by
  have hproductive := measurable_productiveIndicator_at_nextBoundary p ids rewards
    C_star C_h eta i s
  have hVprev := GeneratedProductiveExitBudget.measurable_prelaunchUninformedIndicator p
    s.val s.isLt.le ids rewards C_star C_h eta i
  have hVprev' := hVprev.mono
    ((GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p).mono'
      (Nat.le_succ s.val)) le_rfl
  have hExit := GeneratedProductiveExitBudget.measurable_exitIncrement_at_next_boundary
    p s ids rewards C_star C_h eta i
  have hVnextBase := hVprev'.sub hExit
  have hVnext : @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) ℝ
      (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (s.val + 1)) inferInstance
      (fun e => GeneratedProductiveExitBudget.prelaunchUninformedIndicator
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
        i (s.val + 1)) := by
    have hrepr :
        (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
          GeneratedProductiveExitBudget.prelaunchUninformedIndicator
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
            i (s.val + 1)) =
        (fun e => GeneratedProductiveExitBudget.prelaunchUninformedIndicator
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
            i s.val -
          GeneratedProductiveExitBudget.exitIncrement
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
            i s) := by
      funext e
      simp [GeneratedProductiveExitBudget.exitIncrement]
    rw [hrepr]
    exact hVnextBase
  have hone : @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) ℝ
      (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (s.val + 1)) inferInstance
      (fun _ => (1 : ℝ)) := measurable_const
  have hfactor := hone.sub hVnext
  have hproduct := hproductive.mul hfactor
  have hrepr :
      (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
        GeneratedProductiveExitBudget.productiveExitIndicator
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
          i s) =
      (fun e => GeneratedBootstrapGainBudget.productiveIndicator
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
          i s *
        (1 - GeneratedProductiveExitBudget.prelaunchUninformedIndicator
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
          i (s.val + 1))) := by
    funext e
    rfl
  rw [hrepr]
  exact hproduct

/-- The actual exit indicator is adapted to the auxiliary filtration at
`s+1`, including the final genuine block and its terminal raw boundary. -/
theorem measurable_productiveExitIndicator_at_heldArmRevealFiltration_succ
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    @Measurable (GeneratedBootstrapBlockFiltrationRepair.Coordinates p) ℝ
      (heldArmRevealFiltration p ids rewards C_star C_h eta i (s.val + 1)) inferInstance
      (fun e => GeneratedProductiveExitBudget.productiveExitIndicator
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
        i s) := by
  exact (measurable_productiveExitIndicator_at_nextBoundary p ids rewards C_star C_h eta i s).mono
    (nextBoundary_le_heldArmRevealFiltration_succ p ids rewards C_star C_h eta i s) le_rfl

/-- The accepted productive exit indicator keeps its pointwise unit-interval
bound on the original coordinates. -/
theorem productiveExitIndicator_mem_Icc (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    GeneratedProductiveExitBudget.productiveExitIndicator
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
      i s ∈ Set.Icc 0 1 :=
  GeneratedProductiveExitBudget.productiveExitIndicator_mem_Icc
    (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
    i s

/-- The productive exit indicator is integrable under the original,
unconditioned bootstrap coordinate law. -/
theorem integrable_productiveExitIndicator_originalLaw (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (s : Fin (n_boot p)) :
    Integrable
      (fun e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p =>
        GeneratedProductiveExitBudget.productiveExitIndicator
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
          i s)
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
  have hmeas := measurable_productiveExitIndicator_at_nextBoundary p ids rewards
    C_star C_h eta i s
  have hmeasAmbient := hmeas.mono
    (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration_le_ambient p (s.val + 1)) le_rfl
  refine Integrable.of_bound hmeasAmbient.aestronglyMeasurable 1 (ae_of_all _ fun e => ?_)
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by
    have h := productiveExitIndicator_mem_Icc p ids rewards C_star C_h eta i s e
    linarith [h.1],
    (productiveExitIndicator_mem_Icc p ids rewards C_star C_h eta i s e).2⟩

/-- The accepted one-exit budget instantiated on the original bootstrap input;
no new telescoping or budget argument is introduced here. -/
theorem productiveExitIndicator_sum_le_one_originalCoordinates
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (i : Follower p.m)
    (r : ℕ) (hr : r ≤ n_boot p)
    (e : GeneratedBootstrapBlockFiltrationRepair.Coordinates p) :
    (∑ s : Fin r, GeneratedProductiveExitBudget.productiveExitIndicator
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
      i ⟨s.val, s.isLt.trans_le hr⟩) ≤ 1 :=
  GeneratedProductiveExitBudget.productiveExit_sum_le_one
    (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
    i r hr

end Bandits.Support.GeneratedHeldArmRevealFiltration

end
