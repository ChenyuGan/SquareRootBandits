/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCoordinatorSampledPrivateReplay

/-!
# Borel measurability of the sampled actual coordinator replay

This file proves joint Borel measurability on the published output, the
accepted finite sampled coordinator input, and the original finite continuous
reward grid.  It codes the existing coordinator block state and uses the
public one-round bootstrap code constructors at each live step.  The sampled
target arms and all original round scalars remain on their accepted carriers.

Sources, relative to `sources/zip4/manuscript/`:
`01_introduction.tex:18-36`, `07_public_setup.tex:27-38,55-114`,
`appendix_b_communication.tex:94-131`, and `06_interruptions.tex:240-296`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActualCoordinatorSampledPrivateReplay
open Bandits.Support.BootstrapCoordinatorRoundMeasurability
open Bandits.Support.ActualInitializationBlockMeasurability
open Bandits.Support.ActualCompleteCoordinatorOwnHistory
open scoped Classical

namespace Bandits.Support.ActualCoordinatorSampledReplayMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev SampledInput (p : Parameters) (n : ℕ) :=
  CompletePublicTable.PublishedOutput p ×
    (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
      ActualCoordinatorSampledPrivateReplay.GridHistory p n)

variable {p : Parameters}
variable {rate : RateInput p}

/-! ## Countable phase code and unchanged continuous base -/

/-- The live branch stores the existing no-launch localCode code.  The launched
branch stores the exact projected continuation code, including the launch
trigger and post-credit monitor state. -/
abbrev ReplayPhaseCode (p : Parameters) :=
  Sum (BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p)
    (ActualInitializationBlockMeasurability.ContinuationCode p)

instance replayPhaseCodeCountable (p : Parameters) : Countable (ReplayPhaseCode p) :=
  inferInstance

instance replayPhaseCodeMeasurableSpace (p : Parameters) :
    MeasurableSpace (ReplayPhaseCode p) := ⊤

/-- The unchanged continuous base selected from the published ID array and
the sampled row index; both telescope constants are carried together. -/
def sampledCoordinatorBase (a b : ℝ) {α : Type*} [MeasurableSpace α]
    (x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α)) :
    BootstrapCoordinatorRoundMeasurability.CoordinatorContinuousBase p :=
  ((x.1.2 x.2.1.1, x.1.1), (a, b))

private theorem measurable_sampledCoordinatorBase (a b : ℝ) {α : Type*}
    [MeasurableSpace α] :
    Measurable (sampledCoordinatorBase (p := p) a b :
      (CompletePublicTable.PublishedOutput p ×
        (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α)) →
        BootstrapCoordinatorRoundMeasurability.CoordinatorContinuousBase p) := by
  let selected : Fin (M p) × CompletePublicTable.PublishedOutput p →
      CompletePublicTable.CompleteRow p := fun z => z.2.2 z.1
  have hselected : Measurable selected := by
    apply measurable_from_prod_countable_right
    intro q
    exact (measurable_pi_apply q).comp measurable_snd
  have hkey : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α) =>
      (x.2.1.1, x.1)) :=
    ((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk measurable_fst)
  have hrow : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α) =>
        x.1.2 x.2.1.1) := by
    exact hselected.comp hkey
  have hids : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α) => x.1.1) :=
    measurable_fst.comp measurable_fst
  change Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α) =>
    ((x.1.2 x.2.1.1, x.1.1), (a, b)))
  exact (hrow.prodMk hids).prodMk
    (measurable_const.prodMk measurable_const)

private theorem measurable_of_countable_key {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] [MeasurableSpace γ] {f : α → γ}
    (key : α → β) (hkey : Measurable key) (branch : β → α → γ)
    (hbranch : ∀ b, Measurable (branch b))
    (hfactor : ∀ x, f x = branch (key x) x) : Measurable f := by
  have hjoint : Measurable (fun z : β × α => branch z.1 z.2) :=
    measurable_from_prod_countable_right (f := fun z : β × α => branch z.1 z.2)
      hbranch
  have hmeas : Measurable (fun x => branch (key x) x) :=
    hjoint.comp (hkey.prodMk measurable_id)
  rw [show f = fun x => branch (key x) x by funext x; exact hfactor x]
  exact hmeas

/-- A prelaunch continuation code readout that retains its complete row and
ID array in `base` and all countable localCode fields in `localCode`. -/
def prelaunchCodeOf (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p) :
    BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p :=
  (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).2

/-- The countable phase tag and localCode fields read from an existing phase. -/
def replayPhaseCodeOf (phase : BootstrapCoordinatorLocalRound.Continuation p) :
    ReplayPhaseCode p :=
  match phase with
  | .prelaunch live => .inl (prelaunchCodeOf live)
  | .launched _ => .inr (ActualInitializationBlockMeasurability.continuationCodeOf phase)

/-- Forget the separate live constructor while retaining the exact output
shape used by `sampledGridReplayCode`. -/
def replayPhaseCodeView (code : ReplayPhaseCode p) :
    ActualInitializationBlockMeasurability.ContinuationCode p :=
  match code with
  | .inl localCode =>
      (localCode.block, (localCode.target,
        (localCode.coordinator, (localCode.monitor.1, none))))
  | .inr continuation => continuation

/-! ## Beginning and stepping the coded actual coordinator -/

/-- The public prepared-round and observation constructors are both applied
to the exact same live-round inputs. -/
private def sampledPreparedAndObservationCodes
    (a b : ℝ)
    (input : BootstrapCoordinatorRoundMeasurability.CoordinatorObserveInput p a b) :=
  (BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRoundCode p
      input.fixed.input input.ownArmScalar,
    BootstrapCoordinatorRoundMeasurability.coordinatorObserveCode p a b input)

/-- Position a live code at the actual finite calendar round.  A boundary
starts the existing block with its sampled arm and initial localCode state; the
monitor is copied without changing its sentinel. -/
private def sampledLocalCodeAtRound
    (sampled : ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p)
    (t : Fin p.T)
    (localCode : BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p) :
    BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p :=
  if t ∈ BootstrapDimensions.calendarBlock p localCode.block then localCode
  else ⟨BootstrapDimensions.roundBlockIndex p t,
    sampled.2.1 (BootstrapDimensions.roundBlockIndex p t),
    BootstrapCoordinatorRoundMeasurability.coordinatorStateCode p
      (BootstrapPhysicalBlock.initialState p), localCode.monitor⟩

/-- A live step's genuine `CoordinatorRoundInput`, with its membership proof
from the unchanged block on ordinary rounds or the actual quotient block at a
boundary. -/
private def sampledCoordinatorRoundInput (a b : ℝ)
    {α : Type*} [MeasurableSpace α]
    (x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α))
    (t : Fin p.T) (localCode : BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p) :
    BootstrapCoordinatorRoundMeasurability.CoordinatorRoundInput p := by
  let current := sampledLocalCodeAtRound x.2.1 t localCode
  refine ⟨sampledCoordinatorBase (p := p) a b x,
    current, t, ?_⟩
  unfold current sampledLocalCodeAtRound
  split
  · assumption
  · exact BootstrapDimensions.round_mem_quotient_block p t

/-- Fixed-constant input to the launch test, preserving the common pair
`(a,b)` from the continuous base. -/
private def sampledCoordinatorFixedRoundInput (a b : ℝ)
    (x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)))
    (t : Fin p.T) (localCode : BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p) :
    BootstrapCoordinatorRoundMeasurability.CoordinatorFixedRoundInput p a b :=
  ⟨sampledCoordinatorRoundInput a b x t localCode, by rfl⟩

/-- One live round's separate own scalar and original finite reward feedback. -/
private def sampledCoordinatorObserveInput (a b : ℝ)
    (x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)))
    (t : Fin p.T) (localCode : BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p) :
    BootstrapCoordinatorRoundMeasurability.CoordinatorObserveInput p a b :=
  ⟨sampledCoordinatorFixedRoundInput a b
      x t localCode,
    x.2.1.2.2 t, x.2.2⟩

/-! ## Measurable one-round code assembly -/

private theorem measurable_sampledLocalCodeAtRound
    (t : Fin p.T) {α : Type*} [MeasurableSpace α]
    (localCode : BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p) :
    Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α) =>
      sampledLocalCodeAtRound (p := p) x.2.1 t localCode) := by
  by_cases hmem : t ∈ BootstrapDimensions.calendarBlock p localCode.block
  · simp [sampledLocalCodeAtRound, hmem]
  · have htarget : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
        (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α) =>
        x.2.1.2.1 (BootstrapDimensions.roundBlockIndex p t)) :=
      (measurable_pi_apply (BootstrapDimensions.roundBlockIndex p t)).comp
        (measurable_fst.comp (measurable_snd.comp
          (measurable_fst.comp measurable_snd)))
    let key := fun x : CompletePublicTable.PublishedOutput p ×
        (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α) =>
      x.2.1.2.1 (BootstrapDimensions.roundBlockIndex p t)
    let branch : Fin p.K →
        (CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α)) →
          BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p :=
      fun target _ =>
      (⟨BootstrapDimensions.roundBlockIndex p t, target,
        BootstrapCoordinatorRoundMeasurability.coordinatorStateCode p
          (BootstrapPhysicalBlock.initialState p), localCode.monitor⟩ :
        BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p)
    have hbranch : ∀ target, Measurable (branch target) := fun _ => measurable_const
    have hfactor : ∀ x, sampledLocalCodeAtRound (p := p) x.2.1 t localCode =
        branch (key x) x := by
      intro x
      simp [key, branch, sampledLocalCodeAtRound, hmem]
    exact measurable_of_countable_key
      (f := fun x => sampledLocalCodeAtRound (p := p) x.2.1 t localCode)
      key htarget branch hbranch hfactor

/-- Positioning changes only the block-local code at a calendar boundary.
The complete row, ID array, and the two constants stay on their original
continuous base; at a boundary the sampled target and source reset are used. -/
private theorem sampledAtRound_coordinates
    (sampled : ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p)
    (t : Fin p.T) (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p) :
    BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p
        (ActualCoordinatorSampledPrivateReplay.sampledAtRound sampled t live) =
      ((BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).1,
        sampledLocalCodeAtRound (p := p) sampled t
          (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).2) := by
  by_cases hmem : t ∈ BootstrapDimensions.calendarBlock p live.data.block
  · simp [ActualCoordinatorSampledPrivateReplay.sampledAtRound, hmem,
      sampledLocalCodeAtRound, BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates]
  · have hreset : BootstrapCoordinatorLocalRound.resetCoordinatorBlockState p
      live.data.coordinator = BootstrapPhysicalBlock.initialState p := by
      cases live.data.coordinator
      rfl
    simp [ActualCoordinatorSampledPrivateReplay.sampledAtRound, hmem,
      ActualCoordinatorSampledPrivateReplay.beginTarget, sampledLocalCodeAtRound,
      BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates,
      BootstrapCoordinatorRoundMeasurability.coordinatorStateCode, hreset]

/-- The complete continuous base carried by either existing continuation. -/
private def sampledPhaseBase
    (phase : BootstrapCoordinatorLocalRound.Continuation p) :
    BootstrapCoordinatorRoundMeasurability.CoordinatorContinuousBase p :=
  let data := ActualInitializationRun.continuationData p phase
  ((data.row, data.ids), (data.C_star, data.C_h))

private theorem sampledAtRound_base
    (sampled : ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p)
    (t : Fin p.T) (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p) :
    sampledPhaseBase (p := p) (.prelaunch
      (ActualCoordinatorSampledPrivateReplay.sampledAtRound sampled t live)) =
      sampledPhaseBase (p := p) (.prelaunch live) := by
  unfold sampledPhaseBase
  simp only [ActualInitializationRun.continuationData]
  unfold ActualCoordinatorSampledPrivateReplay.sampledAtRound
  split <;> rfl

private theorem sampledStep_base
    (sampled : ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p)
    (t : Fin p.T) (phase : BootstrapCoordinatorLocalRound.Continuation p)
    (y : Fin (D p + 1)) :
    sampledPhaseBase (p := p)
        (ActualCoordinatorSampledPrivateReplay.sampledStep sampled t phase y) =
      sampledPhaseBase (p := p) phase := by
  cases phase with
  | launched launch => rfl
  | prelaunch live =>
      let current := ActualCoordinatorSampledPrivateReplay.sampledAtRound sampled t live
      have hmem := ActualCoordinatorSampledPrivateReplay.sampledAtRound_mem sampled t live
      have hdata := ActualInitializationRun.continuationAfterObservation_data p
        current.data current.monitor current.data.coordinator t hmem y
      change (((ActualInitializationRun.continuationData p
          (BootstrapCoordinatorLocalRound.continuationAfterObservation p current.data
            current.monitor current.data.coordinator t hmem y)).row,
        (ActualInitializationRun.continuationData p
          (BootstrapCoordinatorLocalRound.continuationAfterObservation p current.data
            current.monitor current.data.coordinator t hmem y)).ids),
        ((ActualInitializationRun.continuationData p
          (BootstrapCoordinatorLocalRound.continuationAfterObservation p current.data
            current.monitor current.data.coordinator t hmem y)).C_star,
        (ActualInitializationRun.continuationData p
          (BootstrapCoordinatorLocalRound.continuationAfterObservation p current.data
            current.monitor current.data.coordinator t hmem y)).C_h)) = _
      rw [hdata]
      simp only [ActualInitializationRun.updateLocalCoordinatorState]
      change sampledPhaseBase (p := p) (.prelaunch current) =
        sampledPhaseBase (p := p) (.prelaunch live)
      exact sampledAtRound_base (p := p) sampled t live

private theorem sampledRaw_base (a b : ℝ) :
    ∀ (n : ℕ) (hn : n ≤ p.T)
      (x : SampledInput p n),
      sampledPhaseBase (p := p)
        (ActualCoordinatorSampledPrivateReplay.sampledRaw x.1 x.2.1 a b n hn
          (fun j => (x.2.2 j).2)) = sampledCoordinatorBase (p := p) a b x := by
  intro n
  induction n with
  | zero =>
      intro hn x
      rfl
  | succ n ih =>
      intro hn x
      let previous : SampledInput p n :=
        (x.1, (x.2.1, fun j => x.2.2 j.castSucc))
      change sampledPhaseBase (p := p)
          (ActualCoordinatorSampledPrivateReplay.sampledStep x.2.1
            ⟨n, by omega⟩
            (ActualCoordinatorSampledPrivateReplay.sampledRaw x.1 x.2.1 a b n
              (by omega) (fun j => (previous.2.2 j).2))
            ((x.2.2 (Fin.last n)).2)) = sampledCoordinatorBase (p := p) a b x
      rw [sampledStep_base]
      have hprev := ih (by omega) previous
      simpa [sampledCoordinatorBase, previous] using hprev

private theorem measurable_sampledCoordinatorRoundInput (a b : ℝ) (t : Fin p.T)
    {α : Type*} [MeasurableSpace α]
    (localCode : BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p) :
    Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α) =>
      sampledCoordinatorRoundInput (p := p) a b x t localCode) := by
  apply (measurable_comap_iff).2
  change Measurable (fun x =>
    (sampledCoordinatorBase (p := p) a b x,
      (sampledLocalCodeAtRound (p := p) x.2.1 t localCode, t)))
  exact (measurable_sampledCoordinatorBase (p := p) a b).prodMk
    ((measurable_sampledLocalCodeAtRound (p := p) t localCode).prodMk
    (measurable_const : Measurable (fun _ : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α) => t)))

private theorem measurable_sampledCoordinatorObserveInput (a b : ℝ) (t : Fin p.T)
    (localCode : BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p) :
    Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
      sampledCoordinatorObserveInput (p := p) a b x t localCode) := by
  apply (measurable_comap_iff).2
  let hround := measurable_sampledCoordinatorRoundInput (p := p) a b t
    (α := Fin (D p + 1)) localCode
  have hfixed : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
      sampledCoordinatorFixedRoundInput a b x t localCode) := by
    apply (measurable_comap_iff).2
    change Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
        sampledCoordinatorRoundInput a b x t localCode)
    exact hround
  have hsample : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
      x.2.1) := measurable_fst.comp measurable_snd
  have hstream : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
      x.2.1.2.2) := measurable_snd.comp (measurable_snd.comp hsample)
  have hscalar : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
      x.2.1.2.2 t) := (measurable_pi_apply t).comp hstream
  have hfeedback : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
      x.2.2) := measurable_snd.comp measurable_snd
  change Measurable (fun x =>
    (sampledCoordinatorFixedRoundInput a b x t localCode,
      (x.2.1.2.2 t, x.2.2)))
  exact hfixed.prodMk (hscalar.prodMk hfeedback)

private theorem measurable_sampledPreparedAndObservationCodes (a b : ℝ) (t : Fin p.T)
    (localCode : BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p) :
    Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
      sampledPreparedAndObservationCodes (p := p) a b
        (sampledCoordinatorObserveInput a b x t localCode)) := by
  let hround := measurable_sampledCoordinatorRoundInput (p := p) a b t
    (α := Fin (D p + 1)) localCode
  have hsample : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
      x.2.1) := measurable_fst.comp measurable_snd
  have hstream : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
      x.2.1.2.2) := measurable_snd.comp (measurable_snd.comp hsample)
  have hscalar : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
      x.2.1.2.2 t) := (measurable_pi_apply t).comp hstream
  have hprepared : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
      BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRoundCode p
        (sampledCoordinatorRoundInput a b x t localCode) (x.2.1.2.2 t)) :=
    (BootstrapCoordinatorRoundMeasurability.measurable_coordinatorPreparedRoundCode p).comp
      (hround.prodMk hscalar)
  have hobserved : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
      BootstrapCoordinatorRoundMeasurability.coordinatorObserveCode p a b
        (sampledCoordinatorObserveInput a b x t localCode)) :=
    (BootstrapCoordinatorRoundMeasurability.measurable_coordinatorObserveCode p a b).comp
      (measurable_sampledCoordinatorObserveInput (p := p) a b t localCode)
  change Measurable (fun x =>
    (BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRoundCode p
      (sampledCoordinatorRoundInput a b x t localCode) (x.2.1.2.2 t),
     BootstrapCoordinatorRoundMeasurability.coordinatorObserveCode p a b
      (sampledCoordinatorObserveInput a b x t localCode)))
  exact hprepared.prodMk hobserved

private instance coordinatorObservationCodeMeasurableSingleton (p : Parameters) :
    MeasurableSingletonClass (BootstrapCoordinatorRoundMeasurability.CoordinatorObservationCode p) where
  measurableSet_singleton code := by
    let fields := BootstrapCoordinatorRoundMeasurability.coordinatorObservationCodeFields p
    have hfields : Measurable fields := comap_measurable fields
    have hset : ({code} : Set (BootstrapCoordinatorRoundMeasurability.CoordinatorObservationCode p)) =
        fields ⁻¹' {fields code} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        rfl
      · intro h
        exact (BootstrapCoordinatorRoundMeasurability.coordinatorObservationCodeFields_injective
          p h)
    rw [hset]
    exact (measurableSet_singleton _).preimage hfields

private abbrev ValidObservationKey (p : Parameters) :=
  {code : BootstrapCoordinatorRoundMeasurability.CoordinatorObservationCode p //
    code.trigger = none →
      code.monitor.crossingBlock = none ∧ code.monitor.launchPosition = p.T}

private instance validObservationKeyMeasurableSingleton (p : Parameters) :
    MeasurableSingletonClass (ValidObservationKey p) where
  measurableSet_singleton key := by
    have hval : Measurable (Subtype.val : ValidObservationKey p →
        BootstrapCoordinatorRoundMeasurability.CoordinatorObservationCode p) :=
      measurable_subtype_coe
    have hset : ({key} : Set (ValidObservationKey p)) =
        Subtype.val ⁻¹' {key.1} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        rfl
      · intro h
        exact Subtype.ext h
    rw [hset]
    exact (measurableSet_singleton _).preimage hval

private def observationKey (a b : ℝ)
    (input : BootstrapCoordinatorRoundMeasurability.CoordinatorObserveInput p a b) :
    ValidObservationKey p := by
  let code := BootstrapCoordinatorRoundMeasurability.coordinatorObserveCode p a b input
  refine ⟨code, ?_⟩
  intro htrigger
  have hnoLaunch : BootstrapCoordinatorRoundMeasurability.coordinatorLaunchDecision
      p a b input.fixed input.feedback ≠ true := by
    intro hlaunch
    have hcode : code.trigger = some
        (BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRound p
          input.fixed.input input.ownArmScalar).round := by
      simp [code, BootstrapCoordinatorRoundMeasurability.coordinatorObserveCode, hlaunch]
    rw [htrigger] at hcode
    cases hcode
  have hfalse : BootstrapCoordinatorRoundMeasurability.coordinatorLaunchDecision
      p a b input.fixed input.feedback = false := by
    cases hlaunch : BootstrapCoordinatorRoundMeasurability.coordinatorLaunchDecision
        p a b input.fixed input.feedback
    · rfl
    · exact (hnoLaunch hlaunch).elim
  simp [code, BootstrapCoordinatorRoundMeasurability.coordinatorObserveCode, hfalse]

private def observationKeyToPhaseCode (key : ValidObservationKey p) : ReplayPhaseCode p :=
  if htrigger : key.1.trigger = none then
    let code := key.1
    .inl ⟨code.block, code.target, code.coordinator,
      ⟨code.monitor, key.2 htrigger⟩⟩
  else
    let code := key.1
    .inr (code.block, (code.target,
      (code.coordinator, (code.monitor, code.trigger))))

/-- Recode the observation constructor's fields as the actual continuation
code.  The source launch decision controls both the code tag and its sentinel. -/
private def sampledObservationPhaseCode
    (a b : ℝ)
    (input : BootstrapCoordinatorRoundMeasurability.CoordinatorObserveInput p a b) :
    ReplayPhaseCode p :=
  observationKeyToPhaseCode (p := p) (observationKey a b input)

/-- The public observe-code reconstruction pins every field of the actual
post-credit continuation to the constructor fields. -/
private theorem decodedSampledObservationCode (a b : ℝ)
    (input : BootstrapCoordinatorRoundMeasurability.CoordinatorFixedRoundInput p a b)
    (code : BootstrapCoordinatorRoundMeasurability.CoordinatorObservationCode p)
    (observed : BootstrapCoordinatorLocalRound.ObservationResult p)
    (h : BootstrapCoordinatorRoundMeasurability.reconstructCoordinatorObservationCode
      p a b input code = some observed) :
    ActualInitializationBlockMeasurability.continuationCodeOf observed.next =
      (code.block, (code.target,
        (code.coordinator, (code.monitor, code.trigger)))) := by
  unfold BootstrapCoordinatorRoundMeasurability.reconstructCoordinatorObservationCode at h
  split_ifs at h <;> cases h <;>
    simp_all [ActualInitializationBlockMeasurability.continuationCodeOf,
      ActualInitializationRun.continuationData,
      BootstrapCoordinatorLocalRound.Continuation.coordinatorState,
      BootstrapCoordinatorLocalRound.Continuation.monitorState,
      BootstrapCoordinatorRoundMeasurability.coordinatorObservationDataOfCode,
      BootstrapCoordinatorRoundMeasurability.coordinatorStateCode,
      BootstrapCoordinatorRoundMeasurability.coordinatorStateOfCode,
      BootstrapCoordinatorRoundMeasurability.monitorCode,
      BootstrapCoordinatorRoundMeasurability.monitorStateOfCode]
  all_goals
    apply BootstrapCoordinatorRoundMeasurability.monitorCodeFields_injective p
    simp_all

private theorem sampledObservationPhaseCode_exact (a b : ℝ)
    (input : BootstrapCoordinatorRoundMeasurability.CoordinatorObserveInput p a b) :
    sampledObservationPhaseCode (p := p) a b input =
      replayPhaseCodeOf (BootstrapCoordinatorRoundMeasurability.coordinatorObserveResult
        p a b input).next := by
  let code := BootstrapCoordinatorRoundMeasurability.coordinatorObserveCode p a b input
  have hfields := decodedSampledObservationCode (p := p) a b input.fixed code
    (BootstrapCoordinatorRoundMeasurability.coordinatorObserveResult p a b input)
    (BootstrapCoordinatorRoundMeasurability.reconstruct_coordinatorObserveCode p a b input)
  cases hnext : (BootstrapCoordinatorRoundMeasurability.coordinatorObserveResult
      p a b input).next with
  | prelaunch live =>
      have htriggerRaw := congrArg
        (fun c : ActualInitializationBlockMeasurability.ContinuationCode p =>
          c.2.2.2.2) hfields
      have htrigger : code.trigger = none := by
        simpa [code, ActualInitializationBlockMeasurability.continuationCodeOf,
          ActualInitializationRun.continuationData, hnext] using htriggerRaw.symm
      have hkey : (observationKey a b input).1.trigger = none := by
        simp [observationKey, code, htrigger]
      have hkeyCode : (observationKey a b input).1 = code := rfl
      have hfields' := hfields
      simp [ActualInitializationBlockMeasurability.continuationCodeOf,
        ActualInitializationRun.continuationData, hnext,
        BootstrapCoordinatorLocalRound.Continuation.coordinatorState,
        BootstrapCoordinatorLocalRound.Continuation.monitorState] at hfields'
      rcases hfields' with ⟨hblock, htarget, hcoordinator, hmonitor, _⟩
      have hlocal : prelaunchCodeOf live =
          ⟨code.block, code.target, code.coordinator,
            ⟨code.monitor, (observationKey a b input).2 hkey⟩⟩ := by
        have hmonitor' :
            (prelaunchCodeOf live).monitor =
              ⟨code.monitor, (observationKey a b input).2 hkey⟩ :=
          Subtype.ext hmonitor
        apply (BootstrapCoordinatorRoundMeasurability.coordinatorLocalCodeFields_injective p)
        simp only [prelaunchCodeOf, BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates,
          Prod.mk.injEq]
        exact ⟨hblock, htarget, hcoordinator, hmonitor'⟩
      simpa [sampledObservationPhaseCode, observationKeyToPhaseCode,
        replayPhaseCodeOf, hkeyCode, htrigger] using
        congrArg (Sum.inl : BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p →
          ReplayPhaseCode p) hlocal.symm
  | launched launch =>
      have htriggerRaw := congrArg
        (fun c : ActualInitializationBlockMeasurability.ContinuationCode p =>
          c.2.2.2.2) hfields
      have htrigger : code.trigger = some launch.triggerRound := by
        simpa [code, ActualInitializationBlockMeasurability.continuationCodeOf,
          ActualInitializationRun.continuationData, hnext] using htriggerRaw.symm
      have hkey : (observationKey a b input).1.trigger = some launch.triggerRound := by
        simp [observationKey, code, htrigger]
      have hkeyCode : (observationKey a b input).1 = code := rfl
      have hfieldsNext := hfields
      rw [hnext] at hfieldsNext
      simpa [sampledObservationPhaseCode, observationKeyToPhaseCode,
        replayPhaseCodeOf, hkeyCode, htrigger] using
        congrArg (Sum.inr : ActualInitializationBlockMeasurability.ContinuationCode p →
          ReplayPhaseCode p) hfieldsNext.symm

/-- At a live sampled round the code input reassembles the exact positioned
prelaunch state. The public prepared and observation reconstructions therefore
read the same arm, update, monitor, and actual launch-triggering feedback. -/
private theorem measurable_sampledObservationPhaseCode (a b : ℝ) (t : Fin p.T)
    (localCode : BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p) :
    Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
      sampledObservationPhaseCode (p := p) a b
        (sampledCoordinatorObserveInput a b x t localCode)) := by
  let input := fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
    sampledCoordinatorObserveInput a b x t localCode
  let keyMap := fun x => observationKey a b (input x)
  have hkey : Measurable keyMap := by
    apply (measurable_comap_iff).2
    have hin : Measurable input := measurable_sampledCoordinatorObserveInput (p := p) a b t localCode
    have hcodes := measurable_sampledPreparedAndObservationCodes (p := p) a b t localCode
    have hobs : Measurable (fun x =>
        BootstrapCoordinatorRoundMeasurability.coordinatorObserveCode p a b (input x)) := by
      change Measurable (fun x =>
        (sampledPreparedAndObservationCodes (p := p) a b (input x)).2)
      exact measurable_snd.comp hcodes
    change Measurable (fun x => BootstrapCoordinatorRoundMeasurability.coordinatorObserveCode
      p a b (input x))
    exact hobs
  have hmap : Measurable (observationKeyToPhaseCode (p := p)) :=
    measurable_of_countable (observationKeyToPhaseCode (p := p))
  exact hmap.comp hkey

/-! ## Finite sampled recursion -/

/-- A single live observation is coded using the already selected sampled
target, round scalar, and actual grid feedback. -/
private def sampledPhaseCodeStep (a b : ℝ) (t : Fin p.T)
    (code : ReplayPhaseCode p)
    (x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) :
    ReplayPhaseCode p :=
  match code with
  | .inl localCode => sampledObservationPhaseCode a b
      (sampledCoordinatorObserveInput a b x t localCode)
  | .inr continuation => .inr continuation

private theorem sampledLivePhaseCodeStep_exact (a b : ℝ) (t : Fin p.T)
    (x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)))
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hbase : (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).1 =
      sampledCoordinatorBase (p := p) a b x) :
    sampledPhaseCodeStep (p := p) a b t
        (.inl (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).2) x =
      replayPhaseCodeOf (ActualCoordinatorSampledPrivateReplay.sampledStep x.2.1 t
        (.prelaunch live) x.2.2) := by
  let localCode := (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).2
  let current := ActualCoordinatorSampledPrivateReplay.sampledAtRound x.2.1 t live
  have hcoords : BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p current =
      (sampledCoordinatorBase (p := p) a b x,
        sampledLocalCodeAtRound (p := p) x.2.1 t localCode) := by
    rw [sampledAtRound_coordinates]
    rw [hbase]
  have hcoordsBase := congrArg Prod.fst hcoords
  have hcoordsLocal := congrArg Prod.snd hcoords
  change (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p current).1 =
      sampledCoordinatorBase (p := p) a b x at hcoordsBase
  change (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p current).2 =
      sampledLocalCodeAtRound (p := p) x.2.1 t localCode at hcoordsLocal
  have hassemble : BootstrapCoordinatorRoundMeasurability.assemblePrelaunch p
      (sampledCoordinatorBase (p := p) a b x)
      (sampledLocalCodeAtRound (p := p) x.2.1 t localCode) = current := by
    rw [← hcoordsBase, ← hcoordsLocal]
    exact BootstrapCoordinatorRoundMeasurability.reconstructPrelaunch p current
  have hmem : t ∈ BootstrapDimensions.calendarBlock p current.data.block :=
    ActualCoordinatorSampledPrivateReplay.sampledAtRound_mem x.2.1 t live
  generalize hcurrent : current = positioned at *
  let roundInput := sampledCoordinatorRoundInput (p := p) a b x t localCode
  have hprepared : BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRound p
      roundInput (x.2.1.2.2 t) =
        BootstrapCoordinatorLocalRound.prepare p positioned t hmem (x.2.1.2.2 t) := by
    change BootstrapCoordinatorLocalRound.prepare p
        (BootstrapCoordinatorRoundMeasurability.assemblePrelaunch p
          (sampledCoordinatorBase (p := p) a b x)
          (sampledLocalCodeAtRound (p := p) x.2.1 t localCode)) t _ _ = _
    cases hassemble
    rfl
  have hobserved :
      (BootstrapCoordinatorRoundMeasurability.coordinatorObserveResult p a b
          (sampledCoordinatorObserveInput (p := p) a b x t localCode)).next =
        (BootstrapCoordinatorLocalRound.observe
          (BootstrapCoordinatorLocalRound.prepare p positioned t hmem (x.2.1.2.2 t))
          x.2.2).next := by
    simp only [BootstrapCoordinatorRoundMeasurability.coordinatorObserveResult,
      sampledCoordinatorObserveInput, sampledCoordinatorFixedRoundInput]
    rw [hprepared]
  calc
    sampledPhaseCodeStep (p := p) a b t
        (.inl (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).2) x =
        sampledObservationPhaseCode (p := p) a b
          (sampledCoordinatorObserveInput (p := p) a b x t localCode) := rfl
    _ = replayPhaseCodeOf (BootstrapCoordinatorRoundMeasurability.coordinatorObserveResult
          p a b (sampledCoordinatorObserveInput (p := p) a b x t localCode)).next :=
        sampledObservationPhaseCode_exact (p := p) a b _
    _ = replayPhaseCodeOf (ActualCoordinatorSampledPrivateReplay.sampledStep x.2.1 t
          (.prelaunch live) x.2.2) := by
      rw [hobserved]
      cases hcurrent
      rfl

private theorem sampledLivePreparedArmCode_exact (a b : ℝ) (t : Fin p.T)
    {α : Type*} [MeasurableSpace α]
    (x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α))
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hbase : (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).1 =
      sampledCoordinatorBase (p := p) a b x) :
    (BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRoundCode p
      (sampledCoordinatorRoundInput (p := p) a b x t
        (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).2)
      (x.2.1.2.2 t)).2.2 =
    (BootstrapCoordinatorLocalRound.prepare p
      (ActualCoordinatorSampledPrivateReplay.sampledAtRound x.2.1 t live) t
      (ActualCoordinatorSampledPrivateReplay.sampledAtRound_mem x.2.1 t live)
      (x.2.1.2.2 t)).arm := by
  let localCode := (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).2
  let current := ActualCoordinatorSampledPrivateReplay.sampledAtRound x.2.1 t live
  have hcoords : BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p current =
      (sampledCoordinatorBase (p := p) a b x,
        sampledLocalCodeAtRound (p := p) x.2.1 t localCode) := by
    rw [sampledAtRound_coordinates, hbase]
  have hcoordsBase := congrArg Prod.fst hcoords
  have hcoordsLocal := congrArg Prod.snd hcoords
  change (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p current).1 =
      sampledCoordinatorBase (p := p) a b x at hcoordsBase
  change (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p current).2 =
      sampledLocalCodeAtRound (p := p) x.2.1 t localCode at hcoordsLocal
  have hassemble : BootstrapCoordinatorRoundMeasurability.assemblePrelaunch p
      (sampledCoordinatorBase (p := p) a b x)
      (sampledLocalCodeAtRound (p := p) x.2.1 t localCode) = current := by
    rw [← hcoordsBase, ← hcoordsLocal]
    exact BootstrapCoordinatorRoundMeasurability.reconstructPrelaunch p current
  have hmem : t ∈ BootstrapDimensions.calendarBlock p current.data.block :=
    ActualCoordinatorSampledPrivateReplay.sampledAtRound_mem x.2.1 t live
  generalize hcurrent : current = positioned at *
  let roundInput := sampledCoordinatorRoundInput (p := p) a b x t localCode
  let preparedCode := BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRoundCode p
      roundInput (x.2.1.2.2 t)
  have hprepared : BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRound p
      roundInput (x.2.1.2.2 t) =
        BootstrapCoordinatorLocalRound.prepare p positioned t hmem (x.2.1.2.2 t) := by
    change BootstrapCoordinatorLocalRound.prepare p
        (BootstrapCoordinatorRoundMeasurability.assemblePrelaunch p
          (sampledCoordinatorBase (p := p) a b x)
          (sampledLocalCodeAtRound (p := p) x.2.1 t localCode)) t _ _ = _
    cases hassemble
    rfl
  have hreconstruction :=
    BootstrapCoordinatorRoundMeasurability.reconstruct_coordinatorPreparedRoundCode p
      roundInput (x.2.1.2.2 t)
  have hdecodedCodeArm :
      (Option.map (fun z : BootstrapCoordinatorLocalRound.PreparedRound p => z.arm)
        (BootstrapCoordinatorRoundMeasurability.reconstructPreparedRound p roundInput
          preparedCode)) = some preparedCode.2.2 := by
    rw [hreconstruction]
    simp [preparedCode, BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRoundCode,
      BootstrapCoordinatorRoundMeasurability.encodePreparedRound]
  have hdecodedSourceArm :
      (Option.map (fun z : BootstrapCoordinatorLocalRound.PreparedRound p => z.arm)
        (BootstrapCoordinatorRoundMeasurability.reconstructPreparedRound p roundInput
          preparedCode)) =
        some (BootstrapCoordinatorLocalRound.prepare p positioned t hmem
          (x.2.1.2.2 t)).arm := by
    rw [hreconstruction, hprepared]
    rfl
  have hcodeArm := hdecodedSourceArm
  rw [hdecodedCodeArm] at hcodeArm
  have harm : preparedCode.2.2 =
      (BootstrapCoordinatorLocalRound.prepare p positioned t hmem
        (x.2.1.2.2 t)).arm := Option.some.inj hcodeArm
  simpa [preparedCode, roundInput, localCode, current, hcurrent] using harm

private theorem measurable_sampledPhaseCodeStep (a b : ℝ) (t : Fin p.T) :
    Measurable (fun z : ReplayPhaseCode p ×
      (CompletePublicTable.PublishedOutput p ×
        (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) =>
      sampledPhaseCodeStep (p := p) a b t z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro code
  cases code with
  | inl localCode =>
      exact measurable_sampledObservationPhaseCode (p := p) a b t localCode
  | inr continuation => exact measurable_const

private def initialLocalCode (target : Fin p.K) :
    BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p :=
  ⟨ActualInitializationRun.firstBlock p, target,
    BootstrapCoordinatorRoundMeasurability.coordinatorStateCode p
      (BootstrapPhysicalBlock.initialState p),
    ⟨BootstrapCoordinatorRoundMeasurability.monitorCode p
      (ActualInitializationRun.initialUnlaunchedMonitor p).1,
      by
        simp [BootstrapCoordinatorRoundMeasurability.monitorCode,
          ActualInitializationRun.initialUnlaunchedMonitor,
          BootstrapLaunchMonitor.initialState]⟩⟩

private def sampledInitialPhaseCode (sampled :
    ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p) : ReplayPhaseCode p :=
  .inl (initialLocalCode (sampled.2.1 (ActualInitializationRun.firstBlock p)))

private theorem measurable_sampledInitialPhaseCode (n : ℕ) :
    Measurable (fun x : SampledInput p n => sampledInitialPhaseCode (p := p) x.2.1) := by
  let codeFromTarget : Fin p.K → ReplayPhaseCode p := fun target =>
    .inl (initialLocalCode target)
  have hcode : Measurable codeFromTarget := measurable_of_countable _
  have hsample : Measurable (fun x : SampledInput p n => x.2.1) :=
    measurable_fst.comp measurable_snd
  have harms : Measurable (fun x : SampledInput p n => x.2.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp hsample)
  exact hcode.comp ((measurable_pi_apply (ActualInitializationRun.firstBlock p)).comp harms)

private theorem sampledInitialPhaseCode_exact
    (published : CompletePublicTable.PublishedOutput p)
    (sampled : ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p)
    (a b : ℝ) :
    sampledInitialPhaseCode (p := p) sampled =
      replayPhaseCodeOf (ActualCoordinatorSampledPrivateReplay.sampledInitial
        published sampled a b) := by
  simp [sampledInitialPhaseCode, initialLocalCode, replayPhaseCodeOf, prelaunchCodeOf,
    ActualCoordinatorSampledPrivateReplay.sampledInitial,
    ActualCoordinatorSampledPrivateReplay.beginTarget,
    BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates,
    BootstrapCoordinatorRoundMeasurability.coordinatorStateCode,
    BootstrapCoordinatorRoundMeasurability.monitorCode,
    BootstrapCoordinatorLocalRound.resetCoordinatorBlockState,
    BootstrapPhysicalBlock.initialState,
    ActualInitializationRun.initialUnlaunchedMonitor,
    BootstrapLaunchMonitor.initialState]

/-- Apply the source's block-position operation to the countable live code.
At `T` it retains the terminal continuation with no extra round. -/
private def sampledPositionPhaseCode (n : ℕ) (_hn : n ≤ p.T)
    (sampled : ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p)
    (code : ReplayPhaseCode p) : ReplayPhaseCode p :=
  match code with
  | .inr continuation => .inr continuation
  | .inl localCode =>
      if htime : n < p.T then
        .inl (sampledLocalCodeAtRound sampled ⟨n, htime⟩ localCode)
      else .inl localCode

private theorem sampledPositionPhaseCode_exact (n : ℕ) (hn : n ≤ p.T)
    (sampled : ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p)
    (phase : BootstrapCoordinatorLocalRound.Continuation p) :
    sampledPositionPhaseCode (p := p) n hn sampled (replayPhaseCodeOf phase) =
      replayPhaseCodeOf
        (ActualCoordinatorSampledPrivateReplay.sampledAtPosition sampled n phase) := by
  cases phase with
  | launched launch => rfl
  | prelaunch live =>
      by_cases htime : n < p.T
      · have hcoords := sampledAtRound_coordinates (p := p) sampled ⟨n, htime⟩ live
        have hlocal := congrArg Prod.snd hcoords
        simpa [sampledPositionPhaseCode, ActualCoordinatorSampledPrivateReplay.sampledAtPosition,
          replayPhaseCodeOf, prelaunchCodeOf, htime] using
          congrArg (Sum.inl : BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p →
            ReplayPhaseCode p) hlocal.symm
      · simp [sampledPositionPhaseCode,
          ActualCoordinatorSampledPrivateReplay.sampledAtPosition,
          replayPhaseCodeOf, prelaunchCodeOf, htime]

private theorem measurable_sampledPositionPhaseCode (n : ℕ) (hn : n ≤ p.T) :
    Measurable (fun z : ReplayPhaseCode p × SampledInput p n =>
      sampledPositionPhaseCode (p := p) n hn z.2.2.1 z.1) := by
  refine measurable_from_prod_countable_right
    (f := fun z : ReplayPhaseCode p × SampledInput p n =>
      sampledPositionPhaseCode (p := p) n hn z.2.2.1 z.1) ?_
  intro code
  cases code with
  | inr continuation => exact measurable_const
  | inl localCode =>
      by_cases htime : n < p.T
      · have hlocal := measurable_sampledLocalCodeAtRound (p := p) ⟨n, htime⟩
          (α := ActualCoordinatorSampledPrivateReplay.GridHistory p n) localCode
        have hinl : Measurable (fun c :
            BootstrapCoordinatorRoundMeasurability.CoordinatorLocalCode p =>
            (Sum.inl c : ReplayPhaseCode p)) := measurable_of_countable _
        simp only [sampledPositionPhaseCode, htime]
        exact hinl.comp hlocal
      · simp [sampledPositionPhaseCode, htime]

/-- The exact finite code recursion for `sampledRaw`; only the source's
coordinator feedback coordinate is consumed from each grid-history entry. -/
private def sampledRawPhaseCode (a b : ℝ) :
    (n : ℕ) → n ≤ p.T → SampledInput p n → ReplayPhaseCode p
  | 0, _, x => sampledInitialPhaseCode (p := p) x.2.1
  | n + 1, hn, x =>
      let previous : SampledInput p n :=
        (x.1, (x.2.1, fun j => x.2.2 j.castSucc))
      let t : Fin p.T := ⟨n, by omega⟩
      sampledPhaseCodeStep (p := p) a b t
        (sampledRawPhaseCode a b n (by omega) previous)
        (x.1, (x.2.1, (x.2.2 (Fin.last n)).2))

private theorem measurable_sampledRawPhaseCode (a b : ℝ) :
    ∀ (n : ℕ) (hn : n ≤ p.T), Measurable (sampledRawPhaseCode (p := p) a b n hn) := by
  intro n
  induction n with
  | zero =>
      intro hn
      exact measurable_sampledInitialPhaseCode (p := p) 0
  | succ n ih =>
      intro hn
      let t : Fin p.T := ⟨n, by omega⟩
      let previousInput : SampledInput p (n + 1) → SampledInput p n := fun x =>
        (x.1, (x.2.1, fun j => x.2.2 j.castSucc))
      have hgrid : Measurable (fun x : SampledInput p (n + 1) => x.2.2) :=
        measurable_snd.comp measurable_snd
      have hprefix : Measurable previousInput := by
        exact measurable_fst.prodMk
          ((measurable_fst.comp measurable_snd).prodMk
            (measurable_pi_iff.mpr (fun j =>
              (measurable_pi_apply j.castSucc).comp hgrid)))
      let stepInput : SampledInput p (n + 1) →
          CompletePublicTable.PublishedOutput p ×
            (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) :=
        fun x => (x.1, (x.2.1, (x.2.2 (Fin.last n)).2))
      have hstep : Measurable stepInput := by
        change Measurable (fun x : SampledInput p (n + 1) =>
          (x.1, (x.2.1, (x.2.2 (Fin.last n)).2)))
        have hlast : Measurable (fun x : SampledInput p (n + 1) =>
            (x.2.2 (Fin.last n)).2) :=
          measurable_snd.comp ((measurable_pi_apply (Fin.last n)).comp hgrid)
        exact measurable_fst.prodMk
          ((measurable_fst.comp measurable_snd).prodMk hlast)
      have hcode := (ih (by omega)).comp hprefix
      have hpair : Measurable (fun x : SampledInput p (n + 1) =>
          (sampledRawPhaseCode (p := p) a b n (by omega) (previousInput x), stepInput x)) :=
        hcode.prodMk hstep
      change Measurable (fun x =>
        sampledPhaseCodeStep (p := p) a b t
          (sampledRawPhaseCode a b n (by omega) (previousInput x)) (stepInput x))
      exact (measurable_sampledPhaseCodeStep (p := p) a b t).comp hpair

private theorem sampledRawPhaseCode_exact (a b : ℝ) :
    ∀ (n : ℕ) (hn : n ≤ p.T) (x : SampledInput p n),
      sampledRawPhaseCode (p := p) a b n hn x =
        replayPhaseCodeOf (ActualCoordinatorSampledPrivateReplay.sampledRaw
          x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2)) := by
  intro n
  induction n with
  | zero =>
      intro hn x
      exact (sampledInitialPhaseCode_exact (p := p) x.1 x.2.1 a b).symm
  | succ n ih =>
      intro hn x
      let previous : SampledInput p n :=
        (x.1, (x.2.1, fun j => x.2.2 j.castSucc))
      let t : Fin p.T := ⟨n, by omega⟩
      let y : Fin (D p + 1) := (x.2.2 (Fin.last n)).2
      let stepInput := (x.1, (x.2.1, y))
      have hprevious := ih (by omega) previous
      change sampledPhaseCodeStep (p := p) a b t
          (sampledRawPhaseCode (p := p) a b n (by omega) previous) stepInput =
        replayPhaseCodeOf (ActualCoordinatorSampledPrivateReplay.sampledStep x.2.1 t
          (ActualCoordinatorSampledPrivateReplay.sampledRaw x.1 x.2.1 a b n (by omega)
            (fun j => (previous.2.2 j).2)) y)
      rw [hprevious]
      cases hphase : ActualCoordinatorSampledPrivateReplay.sampledRaw x.1 x.2.1 a b n
          (by omega) (fun j => (previous.2.2 j).2) with
      | launched launch =>
          simp [sampledPhaseCodeStep, replayPhaseCodeOf,
            ActualCoordinatorSampledPrivateReplay.sampledStep]
      | prelaunch live =>
          have hbaseRaw := sampledRaw_base (p := p) a b n (by omega) previous
          rw [hphase] at hbaseRaw
          have hbase : (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).1 =
              sampledCoordinatorBase (p := p) a b stepInput := by
            simpa [sampledPhaseBase,
              ActualInitializationRun.continuationData,
              BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates,
              sampledCoordinatorBase, previous, stepInput] using hbaseRaw
          simpa [replayPhaseCodeOf, prelaunchCodeOf] using
            sampledLivePhaseCodeStep_exact (p := p) a b t stepInput live hbase

private theorem sampledInitPhaseCode_exact (a b : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (x : SampledInput p n) :
    sampledPositionPhaseCode (p := p) n hn x.2.1
        (sampledRawPhaseCode (p := p) a b n hn x) =
      replayPhaseCodeOf (ActualCoordinatorSampledPrivateReplay.sampledInit
        x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2)) := by
  unfold ActualCoordinatorSampledPrivateReplay.sampledInit
  rw [sampledRawPhaseCode_exact]
  exact sampledPositionPhaseCode_exact (p := p) n hn x.2.1 _

private theorem sampledInit_base (a b : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (x : SampledInput p n) :
    sampledPhaseBase (p := p)
        (ActualCoordinatorSampledPrivateReplay.sampledInit
          x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2)) =
      sampledCoordinatorBase (p := p) a b x := by
  have hraw := sampledRaw_base (p := p) a b n hn x
  unfold ActualCoordinatorSampledPrivateReplay.sampledInit
  cases hphase : ActualCoordinatorSampledPrivateReplay.sampledRaw x.1 x.2.1 a b n hn
      (fun j => (x.2.2 j).2) with
  | launched launch =>
      simpa [ActualCoordinatorSampledPrivateReplay.sampledAtPosition, hphase] using hraw
  | prelaunch live =>
      rw [hphase] at hraw
      by_cases htime : n < p.T
      · have hposition := sampledAtRound_base (p := p) x.2.1 ⟨n, htime⟩ live
        simpa [ActualCoordinatorSampledPrivateReplay.sampledAtPosition, htime] using
          hposition.trans hraw
      · simpa [ActualCoordinatorSampledPrivateReplay.sampledAtPosition, htime] using hraw

private theorem replayPhaseCodeView_exact
    (phase : BootstrapCoordinatorLocalRound.Continuation p) :
    replayPhaseCodeView (p := p) (replayPhaseCodeOf phase) =
      ActualInitializationBlockMeasurability.continuationCodeOf phase := by
  cases phase with
  | prelaunch live =>
      simp [replayPhaseCodeView, replayPhaseCodeOf, prelaunchCodeOf,
        ActualInitializationBlockMeasurability.continuationCodeOf,
        ActualInitializationRun.continuationData,
        BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates,
        BootstrapCoordinatorLocalRound.Continuation.coordinatorState,
        BootstrapCoordinatorLocalRound.Continuation.monitorState]
  | launched launch => rfl

/-! ## Ordinary code, retaining its UP bank -/

private theorem measurable_sampledSelectedRow {α : Type*} [MeasurableSpace α] :
    Measurable (fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α) =>
      x.1.2 x.2.1.1) := by
  let key := fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α) => x.2.1.1
  let branch : Fin (M p) →
      (CompletePublicTable.PublishedOutput p ×
        (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × α)) →
        CompletePublicTable.CompleteRow p := fun i x => x.1.2 i
  have hkey : Measurable key :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hbranch : ∀ i, Measurable (branch i) := fun i =>
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  exact measurable_of_countable_key (f := fun x => x.1.2 x.2.1.1)
    key hkey branch hbranch (fun _ => rfl)

private theorem measurable_sampledOrdinaryCodeStep (t : Fin p.T) :
    Measurable (fun z :
      (CompletePublicTable.PublishedOutput p ×
        (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) ×
          ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate =>
      ActualCoordinatorSampledPrivateReplay.sampledOrdinaryStep
        z.1.1 z.1.2.1 t z.2 z.1.2.2) := by
  let selectedRow := fun x : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) =>
    x.1.2 x.2.1.1
  let localInput := fun z :
      (CompletePublicTable.PublishedOutput p ×
        (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) ×
          ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate =>
    ((z.2.1, (z.2.2, (selectedRow z.1, t))), z.1.2.2)
  have hrow : Measurable selectedRow := measurable_sampledSelectedRow (p := p)
  have hlocal : Measurable localInput := by
    change Measurable (fun z :
      (CompletePublicTable.PublishedOutput p ×
        (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) ×
          ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate =>
      ((z.2.1, (z.2.2, (selectedRow z.1, t))), z.1.2.2))
    have hrowInput : Measurable (fun z :
        (CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate => selectedRow z.1) :=
      hrow.comp measurable_fst
    have hordinary : Measurable (fun z :
        (CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate => z.2) := measurable_snd
    have hcode : Measurable (fun z :
        (CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate => z.2.1) :=
      measurable_fst.comp hordinary
    have hbank : Measurable (fun z :
        (CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate => z.2.2) :=
      measurable_snd.comp hordinary
    have htime : Measurable (fun _ :
        (CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate => t) := measurable_const
    have hrowTime : Measurable (fun z :
        (CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate =>
        (selectedRow z.1, t)) := hrowInput.prodMk htime
    have hconfig : Measurable (fun z :
        (CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate =>
        (z.2.1, (z.2.2, (selectedRow z.1, t)))) :=
      hcode.prodMk (hbank.prodMk hrowTime)
    have hfeedback : Measurable (fun z :
        (CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate => z.1.2.2) :=
      measurable_snd.comp (measurable_snd.comp measurable_fst)
    exact hconfig.prodMk hfeedback
  have hobserved :=
    (OrdinaryCoordinatorObservationMeasurability.measurable_observeLocalCode
      (p := p) (rate := rate)).comp hlocal
  change Measurable (fun z =>
    ((OrdinaryCoordinatorObservationMeasurability.observeLocalCode
        (p := p) (rate := rate) (localInput z)).1,
      (OrdinaryCoordinatorObservationMeasurability.observeLocalCode
        (p := p) (rate := rate) (localInput z)).2.1))
  exact (measurable_fst.comp hobserved).prodMk
    (measurable_fst.comp (measurable_snd.comp hobserved))

private def sampledOrdinaryPhaseCodeStep (t : Fin p.T)
    (phaseCode : ReplayPhaseCode p)
    (input : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)))
    (code : ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) :
    ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate :=
  match phaseCode with
  | .inl _ => ActualCompleteCoordinatorOwnHistory.initialOrdinaryCode rate
  | .inr _ => ActualCoordinatorSampledPrivateReplay.sampledOrdinaryStep
      input.1 input.2.1 t code input.2.2

private theorem measurable_sampledOrdinaryPhaseCodeStep (t : Fin p.T) :
    Measurable (fun z : ReplayPhaseCode p ×
      ((CompletePublicTable.PublishedOutput p ×
        (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1))) ×
          ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) =>
      sampledOrdinaryPhaseCodeStep (p := p) t z.1 z.2.1 z.2.2) := by
  apply measurable_from_prod_countable_right
  intro phaseCode
  cases phaseCode with
  | inl code => exact measurable_const
  | inr code => exact measurable_sampledOrdinaryCodeStep (p := p) t

private def sampledOrdinaryPhaseCode (rate : RateInput p) (a b : ℝ) :
    (n : ℕ) → n ≤ p.T → SampledInput p n →
      ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate
  | 0, _, _ => ActualCompleteCoordinatorOwnHistory.initialOrdinaryCode rate
  | n + 1, hn, x =>
      let previous : SampledInput p n :=
        (x.1, (x.2.1, fun j => x.2.2 j.castSucc))
      let t : Fin p.T := ⟨n, by omega⟩
      let phaseCode := sampledPositionPhaseCode (p := p) n (by omega) x.2.1
        (sampledRawPhaseCode (p := p) a b n (by omega) previous)
      let input := (x.1, (x.2.1, (x.2.2 (Fin.last n)).2))
      sampledOrdinaryPhaseCodeStep (p := p) t phaseCode input
        (sampledOrdinaryPhaseCode rate a b n (by omega) previous)

private theorem measurable_sampledOrdinaryPhaseCode (rate : RateInput p) (a b : ℝ) :
    ∀ (n : ℕ) (hn : n ≤ p.T),
      Measurable (sampledOrdinaryPhaseCode (p := p) rate a b n hn) := by
  intro n
  induction n with
  | zero =>
      intro hn
      exact measurable_const
  | succ n ih =>
      intro hn
      let previousInput : SampledInput p (n + 1) → SampledInput p n := fun x =>
        (x.1, (x.2.1, fun j => x.2.2 j.castSucc))
      have hgrid : Measurable (fun x : SampledInput p (n + 1) => x.2.2) :=
        measurable_snd.comp measurable_snd
      have hprefix : Measurable previousInput := by
        exact measurable_fst.prodMk
          ((measurable_fst.comp measurable_snd).prodMk
            (measurable_pi_iff.mpr (fun j =>
              (measurable_pi_apply j.castSucc).comp hgrid)))
      let phaseInput : SampledInput p (n + 1) → ReplayPhaseCode p × SampledInput p n :=
        fun x => (sampledRawPhaseCode (p := p) a b n (by omega) (previousInput x),
          previousInput x)
      have hphaseInput : Measurable phaseInput := by
        have hraw := (measurable_sampledRawPhaseCode (p := p) a b n (by omega)).comp hprefix
        exact hraw.prodMk hprefix
      have hphase : Measurable (fun x : SampledInput p (n + 1) =>
          sampledPositionPhaseCode (p := p) n (by omega)
            (phaseInput x).2.2.1 (phaseInput x).1) :=
        (measurable_sampledPositionPhaseCode (p := p) n (by omega)).comp hphaseInput
      let stepInput : SampledInput p (n + 1) →
          CompletePublicTable.PublishedOutput p ×
            (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p × Fin (D p + 1)) :=
        fun x => (x.1, (x.2.1, (x.2.2 (Fin.last n)).2))
      have hstep : Measurable stepInput := by
        have hlast : Measurable (fun x : SampledInput p (n + 1) =>
            (x.2.2 (Fin.last n)).2) :=
          measurable_snd.comp ((measurable_pi_apply (Fin.last n)).comp hgrid)
        exact measurable_fst.prodMk
          ((measurable_fst.comp measurable_snd).prodMk hlast)
      have hpreviousCode := (ih (by omega)).comp hprefix
      let previousCode := fun x : SampledInput p (n + 1) =>
        sampledOrdinaryPhaseCode (p := p) rate a b n (by omega) (previousInput x)
      have hinput : Measurable (fun x : SampledInput p (n + 1) =>
          (stepInput x, previousCode x)) := hstep.prodMk hpreviousCode
      have hpair : Measurable (fun x : SampledInput p (n + 1) =>
          (sampledPositionPhaseCode (p := p) n (by omega)
            (phaseInput x).2.2.1 (phaseInput x).1,
            (stepInput x, previousCode x))) := hphase.prodMk hinput
      change Measurable (fun x => sampledOrdinaryPhaseCodeStep (p := p)
        ⟨n, by omega⟩
        (sampledPositionPhaseCode (p := p) n (by omega)
          (phaseInput x).2.2.1 (phaseInput x).1)
        (stepInput x) (previousCode x))
      exact (measurable_sampledOrdinaryPhaseCodeStep (p := p) ⟨n, by omega⟩).comp hpair

private theorem sampledOrdinaryPhaseCode_exact (rate : RateInput p) (a b : ℝ) :
    ∀ (n : ℕ) (hn : n ≤ p.T) (x : SampledInput p n),
      sampledOrdinaryPhaseCode (p := p) rate a b n hn x =
        ActualCoordinatorSampledPrivateReplay.sampledOrdinary rate x.1 x.2.1 a b n hn
          (fun j => (x.2.2 j).2) := by
  intro n
  induction n with
  | zero =>
      intro hn x
      rfl
  | succ n ih =>
      intro hn x
      let previous : SampledInput p n :=
        (x.1, (x.2.1, fun j => x.2.2 j.castSucc))
      let t : Fin p.T := ⟨n, by omega⟩
      let stepInput := (x.1, (x.2.1, (x.2.2 (Fin.last n)).2))
      have hprevious := ih (by omega) previous
      have hphase := sampledInitPhaseCode_exact (p := p) a b n (by omega) previous
      change sampledOrdinaryPhaseCodeStep (p := p) t
          (sampledPositionPhaseCode (p := p) n (by omega) x.2.1
            (sampledRawPhaseCode (p := p) a b n (by omega) previous))
          stepInput (sampledOrdinaryPhaseCode (p := p) rate a b n (by omega) previous) =
        (match ActualCoordinatorSampledPrivateReplay.sampledInit x.1 x.2.1 a b n
            (by omega) (fun j => (previous.2.2 j).2) with
        | .prelaunch _ => ActualCompleteCoordinatorOwnHistory.initialOrdinaryCode rate
        | .launched _ =>
            ActualCoordinatorSampledPrivateReplay.sampledOrdinaryStep x.1 x.2.1 t
              (ActualCoordinatorSampledPrivateReplay.sampledOrdinary rate x.1 x.2.1 a b n
                (by omega) (fun j => (previous.2.2 j).2)) (stepInput.2.2))
      rw [hphase]
      cases hsource : ActualCoordinatorSampledPrivateReplay.sampledInit x.1 x.2.1 a b n
          (by omega) (fun j => (previous.2.2 j).2) with
      | prelaunch live =>
          simp [sampledOrdinaryPhaseCodeStep, replayPhaseCodeOf]
      | launched launch =>
          simp [sampledOrdinaryPhaseCodeStep, replayPhaseCodeOf]
          rw [hprevious]

/-- Joint Borel measurability of the actual sampled coordinator continuation
and ordinary code after every finite original feedback prefix, including the
terminal prefix at `T`. -/
theorem measurable_sampledGridReplayCode (rate : RateInput p) (a b : ℝ)
    (n : ℕ) (hn : n ≤ p.T) :
    Measurable (ActualCoordinatorSampledPrivateReplay.sampledGridReplayCode
      rate a b n hn) := by
  let phaseCode := fun x : SampledInput p n =>
    sampledPositionPhaseCode (p := p) n hn x.2.1
      (sampledRawPhaseCode (p := p) a b n hn x)
  let ordinaryCode := fun x : SampledInput p n =>
    sampledOrdinaryPhaseCode (p := p) rate a b n hn x
  have hraw := measurable_sampledRawPhaseCode (p := p) a b n hn
  have hpositionInput : Measurable (fun x : SampledInput p n =>
      (sampledRawPhaseCode (p := p) a b n hn x, x)) := hraw.prodMk measurable_id
  have hphase : Measurable phaseCode := by
    change Measurable (fun x : SampledInput p n =>
      sampledPositionPhaseCode (p := p) n hn x.2.1
        (sampledRawPhaseCode (p := p) a b n hn x))
    exact (measurable_sampledPositionPhaseCode (p := p) n hn).comp hpositionInput
  have hview : Measurable (fun x => replayPhaseCodeView (p := p) (phaseCode x)) :=
    (measurable_of_countable (replayPhaseCodeView (p := p))).comp hphase
  have hordinary : Measurable ordinaryCode :=
    measurable_sampledOrdinaryPhaseCode (p := p) rate a b n hn
  have hfirstExact :
      (fun x : SampledInput p n =>
        ActualInitializationBlockMeasurability.continuationCodeOf
          (ActualCoordinatorSampledPrivateReplay.sampledInit
            x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2))) =
      (fun x => replayPhaseCodeView (p := p) (phaseCode x)) := by
    funext x
    dsimp [phaseCode]
    have hcode := sampledInitPhaseCode_exact (p := p) a b n hn x
    rw [hcode]
    exact (replayPhaseCodeView_exact (p := p) _).symm
  have hsecondExact :
      (fun x : SampledInput p n =>
        ActualCoordinatorSampledPrivateReplay.sampledOrdinary rate
          x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2)) = ordinaryCode := by
    funext x
    exact (sampledOrdinaryPhaseCode_exact (p := p) rate a b n hn x).symm
  have hpairExact :
      (fun x : SampledInput p n =>
        (ActualInitializationBlockMeasurability.continuationCodeOf
            (ActualCoordinatorSampledPrivateReplay.sampledInit
              x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2)),
          ActualCoordinatorSampledPrivateReplay.sampledOrdinary rate
            x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2))) =
      (fun x => (replayPhaseCodeView (p := p) (phaseCode x), ordinaryCode x)) := by
    funext x
    exact Prod.ext (congrFun hfirstExact x) (congrFun hsecondExact x)
  change Measurable (fun x : SampledInput p n =>
    (ActualInitializationBlockMeasurability.continuationCodeOf
        (ActualCoordinatorSampledPrivateReplay.sampledInit
          x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2)),
      ActualCoordinatorSampledPrivateReplay.sampledOrdinary rate
        x.1 x.2.1 a b n hn (fun j => (x.2.2 j).2)))
  rw [hpairExact]
  exact hview.prodMk hordinary

/-! ## Current coordinator decision -/

private def sampledDecisionPhaseCodeStep (rate : RateInput p) (a b : ℝ)
    (t : Fin p.T) (phaseCode : ReplayPhaseCode p)
    (input : CompletePublicTable.PublishedOutput p ×
      (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
        ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate)) : Fin p.K :=
  match phaseCode with
  | .inl localCode =>
      (BootstrapCoordinatorRoundMeasurability.coordinatorPreparedRoundCode p
        (sampledCoordinatorRoundInput (p := p) a b
          (input.1, (input.2.1, ())) t localCode)
        (input.2.1.2.2 t)).2.2
  | .inr _ =>
      let localInput : OrdinaryCoordinatorLocalMeasurability.LocalInput p rate :=
        (input.2.2.1,
          (input.2.2.2, (input.1.2 input.2.1.1, t)))
      (OrdinaryCoordinatorLocalMeasurability.cut localInput).arm

private theorem measurable_sampledDecisionPhaseCodeStep (rate : RateInput p)
    (a b : ℝ) (t : Fin p.T) :
    Measurable (fun z : ReplayPhaseCode p ×
      (CompletePublicTable.PublishedOutput p ×
        (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
          ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate)) =>
      sampledDecisionPhaseCodeStep (p := p) rate a b t z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro phaseCode
  cases phaseCode with
  | inl localCode =>
      let unitInput := fun x : CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) =>
        (x.1, (x.2.1, ()))
      have hunitInput : Measurable unitInput := by
        change Measurable (fun x : CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) =>
          (x.1, (x.2.1, ())))
        exact measurable_fst.prodMk
          ((measurable_fst.comp measurable_snd).prodMk measurable_const)
      have hround := (measurable_sampledCoordinatorRoundInput (p := p) a b t
        (α := Unit) localCode).comp hunitInput
      have hsample : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) => x.2.1) :=
        measurable_fst.comp measurable_snd
      have hstream : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) => x.2.1.2.2) :=
        measurable_snd.comp (measurable_snd.comp hsample)
      have hscalar : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) =>
          x.2.1.2.2 t) := (measurable_pi_apply t).comp hstream
      have hpreparedCode :=
        (BootstrapCoordinatorRoundMeasurability.measurable_coordinatorPreparedRoundCode p).comp
          (hround.prodMk hscalar)
      exact measurable_snd.comp (measurable_snd.comp hpreparedCode)
  | inr _ =>
      let unitInput := fun x : CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) =>
        (x.1, (x.2.1, ()))
      have hunitInput : Measurable unitInput := by
        change Measurable (fun x : CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) =>
          (x.1, (x.2.1, ())))
        exact measurable_fst.prodMk
          ((measurable_fst.comp measurable_snd).prodMk measurable_const)
      have hrowBase := (measurable_sampledSelectedRow (p := p) (α := Unit)).comp hunitInput
      let localInput := fun x : CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) =>
        (x.2.2.1, (x.2.2.2, (x.1.2 x.2.1.1, t)))
      have hordinary : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) => x.2.2) :=
        measurable_snd.comp measurable_snd
      have hcode : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) => x.2.2.1) :=
        measurable_fst.comp hordinary
      have hbank : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) => x.2.2.2) :=
        measurable_snd.comp hordinary
      have hrowTime : Measurable (fun x : CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) =>
          (x.1.2 x.2.1.1, t)) := hrowBase.prodMk measurable_const
      have hlocal : Measurable localInput := by
        change Measurable (fun x : CompletePublicTable.PublishedOutput p ×
          (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
            ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) =>
          (x.2.2.1, (x.2.2.2, (x.1.2 x.2.1.1, t))))
        exact hcode.prodMk (hbank.prodMk hrowTime)
      change Measurable (fun x : CompletePublicTable.PublishedOutput p ×
        (ActualCoordinatorSampledPrivateReplay.SampledCoordinatorInput p ×
          ActualCompleteCoordinatorOwnHistory.OrdinaryCode p rate) =>
        (OrdinaryCoordinatorLocalMeasurability.cut (localInput x)).arm)
      exact (OrdinaryCoordinatorPreparationSelectionMeasurability.measurable_prepareLocalArm
        (p := p) (rate := rate)).comp hlocal

private theorem sampledGridDecision_codeExact (rate : RateInput p) (a b : ℝ)
    (t : Fin p.T) (x : SampledInput p t.val) :
    sampledDecisionPhaseCodeStep (p := p) rate a b t
      (sampledPositionPhaseCode (p := p) t.val t.isLt.le x.2.1
        (sampledRawPhaseCode (p := p) a b t.val t.isLt.le x))
      (x.1, (x.2.1,
        sampledOrdinaryPhaseCode (p := p) rate a b t.val t.isLt.le x)) =
      ActualCoordinatorSampledPrivateReplay.sampledGridDecision rate a b t x := by
  have hphase := sampledInitPhaseCode_exact (p := p) a b t.val t.isLt.le x
  have hordinary := sampledOrdinaryPhaseCode_exact (p := p) rate a b t.val t.isLt.le x
  rw [hphase, hordinary]
  cases hinit : ActualCoordinatorSampledPrivateReplay.sampledInit x.1 x.2.1 a b
      t.val t.isLt.le (fun j => (x.2.2 j).2) with
  | prelaunch live =>
      have hbaseInit := sampledInit_base (p := p) a b t.val t.isLt.le x
      rw [hinit] at hbaseInit
      have hbase : (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates p live).1 =
          sampledCoordinatorBase (p := p) a b (x.1, (x.2.1, ())) := by
        simpa [sampledPhaseBase,
          ActualInitializationRun.continuationData,
          BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates,
          sampledCoordinatorBase] using hbaseInit
      have harm := sampledLivePreparedArmCode_exact (p := p) a b t
        (x.1, (x.2.1, ())) live hbase
      simpa [sampledDecisionPhaseCodeStep,
        ActualCoordinatorSampledPrivateReplay.sampledGridDecision,
        replayPhaseCodeOf, prelaunchCodeOf, hinit] using harm
  | launched launch =>
      simp [sampledDecisionPhaseCodeStep,
        ActualCoordinatorSampledPrivateReplay.sampledGridDecision,
        ActualCompleteCoordinatorOwnHistory.decodeOrdinary,
        OrdinaryCoordinatorLocalMeasurability.cut,
        OrdinaryCoordinatorLocalMeasurability.decodedCoordinator,
        OrdinaryCoordinatorLocalMeasurability.coordinatorCode,
        OrdinaryCoordinatorLocalMeasurability.decoderBank,
        OrdinaryCoordinatorLocalMeasurability.completeRow,
        OrdinaryCoordinatorLocalMeasurability.calendarTime,
        replayPhaseCodeOf, hinit]

/-- Joint Borel measurability of the sampled coordinator's current decision
at each actual round, using the exact finite reward prefix and sampled private
input. -/
theorem measurable_sampledGridDecision (rate : RateInput p) (a b : ℝ)
    (t : Fin p.T) :
    Measurable (ActualCoordinatorSampledPrivateReplay.sampledGridDecision
      rate a b t) := by
  let phaseCode := fun x : SampledInput p t.val =>
    sampledPositionPhaseCode (p := p) t.val t.isLt.le x.2.1
      (sampledRawPhaseCode (p := p) a b t.val t.isLt.le x)
  let ordinaryCode := fun x : SampledInput p t.val =>
    sampledOrdinaryPhaseCode (p := p) rate a b t.val t.isLt.le x
  let decisionInput := fun x : SampledInput p t.val =>
    (x.1, (x.2.1, ordinaryCode x))
  have hraw := measurable_sampledRawPhaseCode (p := p) a b t.val t.isLt.le
  have hpositionInput : Measurable (fun x : SampledInput p t.val =>
      (sampledRawPhaseCode (p := p) a b t.val t.isLt.le x, x)) := hraw.prodMk measurable_id
  have hphase : Measurable phaseCode := by
    change Measurable (fun x : SampledInput p t.val =>
      sampledPositionPhaseCode (p := p) t.val t.isLt.le x.2.1
        (sampledRawPhaseCode (p := p) a b t.val t.isLt.le x))
    exact (measurable_sampledPositionPhaseCode (p := p) t.val t.isLt.le).comp
      hpositionInput
  have hordinary : Measurable ordinaryCode :=
    measurable_sampledOrdinaryPhaseCode (p := p) rate a b t.val t.isLt.le
  have hdecisionInput : Measurable decisionInput := by
    change Measurable (fun x : SampledInput p t.val =>
      (x.1, (x.2.1, ordinaryCode x)))
    exact measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk hordinary)
  have hpair : Measurable (fun x : SampledInput p t.val =>
      (phaseCode x, decisionInput x)) := hphase.prodMk hdecisionInput
  have hcoded : Measurable (fun x : SampledInput p t.val =>
      sampledDecisionPhaseCodeStep (p := p) rate a b t (phaseCode x)
        (decisionInput x)) :=
    (measurable_sampledDecisionPhaseCodeStep (p := p) rate a b t).comp hpair
  have hexact :
      (fun x : SampledInput p t.val =>
        ActualCoordinatorSampledPrivateReplay.sampledGridDecision rate a b t x) =
      (fun x => sampledDecisionPhaseCodeStep (p := p) rate a b t
        (phaseCode x) (decisionInput x)) := by
    funext x
    exact (sampledGridDecision_codeExact (p := p) rate a b t x).symm
  change Measurable (fun x : SampledInput p t.val =>
    ActualCoordinatorSampledPrivateReplay.sampledGridDecision rate a b t x)
  rw [hexact]
  exact hcoded

end Bandits.Support.ActualCoordinatorSampledReplayMeasurability

end
