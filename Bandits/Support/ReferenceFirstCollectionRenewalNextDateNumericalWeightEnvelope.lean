/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep
public import Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalWeightEnvelope
public import Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix
public import Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView
public import Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix
public import Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueBounds
public import Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix
public import Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments
public import Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw
public import Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling
public import Bandits.Support.ReferenceFirstCollectionRenewalControlFactor

import Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability
import Bandits.Support.ReferenceDownReceptionMeasurability
import Bandits.Support.ReferenceCollectionDispatchMeasurability
import Bandits.Support.ReplayWeightStability
import Bandits.Support.FollowerCutoffScan

import Mathlib.Tactic

/-!
# The immediate next-date numerical weight envelope

The actual next sender view and optional numerical cell are read from the
original next record. On the retained next-date event, the numerical score
weight includes exactly the renewal cell once and has the canonical marginal
cost bound on the original unnormalized renewal law.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:151-187,256-318`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`, and
`sources/zip4/manuscript/06_interruptions.tex:391-426`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical MeasureTheory

namespace Bandits.Support.ReferenceFirstCollectionRenewalNextDateNumericalWeightEnvelope

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

abbrev Source :=
  Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.Source
    rate rewards C_star C_h u t

local notation "Z" => Source rate rewards C_star C_h u t
local notation "B" =>
  Bandits.Support.ReferenceFirstCollectionRenewalControlFactor.Pair
    rate rewards C_star C_h u t
local notation "ν" =>
  Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
    rate rewards C_star C_h u t
local notation "μ" =>
  Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
    rate rewards C_star C_h u t

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- The register vector after the actual current renewal cell. -/
def A (z : Z) : Fin p.K → ℕ × ℕ :=
  (Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z).registers

/-- The literal next-date numerical score weight, including the actual
renewal update exactly once. -/
def w (z : Z) (j : Fin p.K) : ℝ :=
  (1 + 1 / (D p : ℝ)) ^ (A rate rewards C_star C_h u t z j).1

/-- The same product-set marginal used by the source rate bound. -/
noncomputable def theta (z : Z) : Fin p.K → ℝ :=
  ProductSetLaw.theta p.m (w rate rewards C_star C_h u t z)

/-- The literal enabled, prior-clear next-date event from the accepted
exponential-step producer. -/
def G (hq : t.val + 1 < p.T) : Set Z :=
  Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate rate rewards C_star C_h u t hq

/-- Measurable elimination of an optional value with an explicit default. -/
private theorem measurable_option_elim {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (f : α → β) (hf : Measurable f) (b : β) :
    Measurable (fun o : Option α => o.elim b f) := by
  have hsum : Measurable (fun o : Option α => Equiv.optionEquivSumPUnit α o) :=
    comap_measurable _
  convert (hf.sumElim measurable_const).comp hsum using 1
  funext o
  cases o <;> rfl

private theorem measurable_view_anchor :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload.anchor) := by
  have hv : Measurable (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
      (p := p) (rate := rate)) := comap_measurable _
  have hp : Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload) := measurable_fst.comp hv
  have ho := (ReferenceCollectionDispatchMeasurability.measurable_payloadObservation
    (p := p) (rate := rate)).comp hp
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp ho)))

/-- The actual next sender's payload is the original payload installed by the
renewal call, and the call's actual selection exposes that same payload. -/
private theorem nextDownView_payload_eq_callSelection
    (hq : t.val + 1 < p.T) (z : Z)
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (hview : (Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator.downView =
      some view)
    (selected : ReferenceActivePhysicalStep.Selection
      (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord rate rewards C_star C_h u t z).input)
    (hselected : (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord rate rewards C_star C_h u t z).output.preparation.coordinator.selection =
      some selected) :
    view.payload = selected.view.payload := by
  have hinstalled := Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextDownView_installed_payload
    rate rewards C_star C_h u t z hq
  cases hcoord : (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord rate rewards C_star C_h u t z).output.preparation.coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hinstruction output hlocal
          clockData installed armSelection =>
        have htime := ReferenceActivePhysicalStep.later_instruction_time
          (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord rate rewards C_star C_h u t z).input payload ledger clock cutoff
          core started instruction hstart hinstruction
        rw [hcoord] at hinstalled hselected
        have hviewInstalled : view.payload = installed.registers.payload := by
          simpa only [Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextDownView, hview] using hinstalled
        have hselection :
            ReferenceActivePhysicalStep.selectionAt
                (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord rate rewards C_star C_h u t z).input
                installed.registers.payload started instruction.time
                installed.registers.complementWeights armSelection = some selected := by
          simpa only [ReferenceActivePhysicalStep.DispatchCut.selection] using hselected
        have hselectedPayload : selected.view.payload = installed.registers.payload := by
          have h := hselection
          simp [ReferenceActivePhysicalStep.selectionAt, htime] at h
          have hpayload := congrArg
            (fun s : ReferenceActivePhysicalStep.Selection
              (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord rate rewards C_star C_h u t z).input => s.view.payload) h.symm
          simpa only using hpayload
        exact hviewInstalled.trans hselectedPayload.symm
      | _ => simp [hcoord] at hinstalled
  | _ => simp [hcoord] at hinstalled

/-- The literal retained event supplies the original optional cell, its actual
sender view, and the same enabled rate vector. The cell's rate is the
canonical rate at that installed view's anchor. -/
theorem G_actual_readouts (hq : t.val + 1 < p.T) (z : Z)
    (hz : z ∈ G rate rewards C_star C_h u t hq) :
    ∃ (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
      (xi : Fin p.K → ℝ) (cell : RecordedQueueRun.RoundInput p.K)
      (selected : ReferenceActivePhysicalStep.Selection
        (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord rate rewards C_star C_h u t z).input),
      (Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator.downView =
        some view ∧
      Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters rate rewards C_star C_h u t z hq = some (true, xi) ∧
      Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq = some cell ∧
      cell.enabled = true ∧ cell.rate = xi ∧
      (∀ j : Fin p.K,
        xi j = CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor j) ∧
      (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord rate rewards C_star C_h u t z).output.preparation.coordinator.selection =
        some selected ∧
      view.payload = selected.view.payload := by
  obtain ⟨⟨xi, hparameters⟩, _hclear⟩ :=
    (Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.mem_retainedNextDate_iff rate rewards C_star C_h u t hq z).mp hz
  cases hcell : Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq with
  | none =>
      simp [Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters, hcell] at hparameters
  | some cell =>
      have hcellParameters : Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters rate rewards C_star C_h u t z hq =
          some (cell.enabled, cell.rate) := by
        simp only [Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters, hcell, Option.map_some]
      have hpair := Option.some.inj (hparameters.symm.trans hcellParameters)
      rcases Prod.mk.inj hpair with ⟨henabled, hxi⟩
      have hcanonicalCell := Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextCell_rate_canonical rate rewards C_star C_h u t z hq
      rw [hcell] at hcanonicalCell
      obtain ⟨view, hview, hrate, hcanonical⟩ := hcanonicalCell
      have hview' :
          (Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator.downView =
            some view := by
        simpa only [Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextDownView] using hview
      obtain ⟨_, selected, hselected, _, _⟩ :=
        Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_numerical rate rewards C_star C_h u t z
      refine ⟨view, xi, cell, selected, hview', hparameters, rfl, ?_, ?_, ?_, hselected,
        ?_⟩
      · exact henabled.symm
      · exact hxi.symm
      · intro j
        exact (congrFun hxi j).trans (hcanonical j)
      · exact nextDownView_payload_eq_callSelection rate rewards C_star C_h u t hq z
          view hview' selected hselected

/-- A clear post-renewal readout forces the incoming queue to be clear: the
actual whole renewal cell is one stopped-queue step, and overflow persists
through that step. -/
theorem G_implies_incoming_clear (hq : t.val + 1 < p.T) (z : Z)
    (hz : z ∈ G rate rewards C_star C_h u t hq) :
    (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t z).overflow = false := by
  have hparts := hz
  simp only [G, Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate, Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow] at hparts
  have hpost : (Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout rate rewards C_star C_h u t z).2.1 = false :=
    hparts.2
  have hcurrent : (Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z).overflow = false := by
    rw [Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout_overflow] at hpost
    simpa only [Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState, Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells] using hpost
  have hrun : Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z =
      RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t z)
        (Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell rate rewards C_star C_h u t z) := by
    change RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells rate rewards C_star C_h u t z ++
          [Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell rate rewards C_star C_h u t z]) = _
    simpa only [Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming] using
      Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.run_append_one rate
        (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells rate rewards C_star C_h u t z)
        (Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell rate rewards C_star C_h u t z)
  have hflag := congrArg (fun state : RecordedQueueRun.RunState p.K => state.overflow) hrun
  rw [hflag] at hcurrent
  exact (Bool.or_eq_false_iff.mp hcurrent).1

def incomingWeight (z : Z) (j : Fin p.K) : ℝ :=
  RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t z) j

/-- The literal per-arm replay of the actual whole renewal cell gives the
one-step numerical score envelope. Its one-record horizon bound follows from
the original source cap on `eta`. -/
theorem G_currentWeight_envelope (hq : t.val + 1 < p.T) (z : Z)
    (hz : z ∈ G rate rewards C_star C_h u t hq) (j : Fin p.K) :
    incomingWeight rate rewards C_star C_h u t z j ≤
        w rate rewards C_star C_h u t z j ∧
      w rate rewards C_star C_h u t z j ≤
        2 * incomingWeight rate rewards C_star C_h u t z j := by
  have hclear := G_implies_incoming_clear rate rewards C_star C_h u t hq z hz
  let cell := Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell rate rewards C_star C_h u t z
  let state := Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t z
  let record := (true, RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell j)
  have hrecord : RecordedQueueRun.acceptedRecord
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) state cell j = record := by
    dsimp only [record, state, cell]
    rw [Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_acceptedRecord rate rewards C_star C_h u t z j, hclear]
    rfl
  have hrun : Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z =
      RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        state cell := by
    change RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells rate rewards C_star C_h u t z ++ [cell]) = _
    simpa only [state, Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming] using
      Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.run_append_one rate
        (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells rate rewards C_star C_h u t z) cell
  have hregister : (Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z).registers j =
      QueueReplay.replay (4 * rate.n) (state.registers j) [record] := by
    rw [hrun]
    change QueueReplay.transition (4 * rate.n) (state.registers j)
        (RecordedQueueRun.acceptedRecord
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) state cell j) =
      QueueReplay.replay (4 * rate.n) (state.registers j) [record]
    rw [hrecord]
    simp [QueueReplay.replay]
  have hH : 0 < ReplayWeightStability.episodeHorizon rate.eta.val :=
    FollowerCutoffScan.episodeHorizon_pos_of_source_cap p rate.eta.val
      rate.eta.property rate.sourceCap
  have hlen : [record].length ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
    simp only [List.length_cons, List.length_nil]
    exact Nat.succ_le_of_lt hH
  have hstable := ReplayWeightStability.replay_source_weight_envelope
    (score := (state.registers j).1) (backlog := (state.registers j).2)
    (D_pos p) rate.eta.val rate.eta.property rate.n_scale.symm [record] hlen
  have hstable' := hstable
  rw [← hregister] at hstable'
  constructor
  · simpa [incomingWeight, w, A, RecordedQueueRun.scoreWeight,
      ReferenceFirstLaunchNumericalCell.queueParameters, ReplayWeightStability.sourceBase,
      ScoreWeights.scoreWeight] using hstable'.1
  · simpa [incomingWeight, w, A, RecordedQueueRun.scoreWeight,
      ReferenceFirstLaunchNumericalCell.queueParameters, ReplayWeightStability.sourceBase,
      ScoreWeights.scoreWeight] using hstable'.2

private theorem measurable_anchorRead (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) :
    Measurable (fun z : Z =>
      (Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextDownView rate rewards C_star C_h u t z hq).elim
        (0 : Fin p.K → ℝ)
        (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta => view.payload.anchor)) := by
  have hle := Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  exact (measurable_option_elim _ (measurable_view_anchor rate)
    (0 : Fin p.K → ℝ)).comp
      ((Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_nextDownView
        rate rewards C_star C_h u t control0 hq).mono hle le_rfl)

/-- On the unchanged pair law, the retained next-date sender anchor is the
same renewal anchor as the incoming numerical score, almost surely on the
literal gate. -/
theorem ae_G_incomingWeight_eq_senderAnchor
    (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    ∀ᵐ z : Z ∂ν,
      z ∈ G rate rewards C_star C_h u t hq →
        (Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextDownView rate rewards C_star C_h u t z hq).elim
          (0 : Fin p.K → ℝ) (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta => view.payload.anchor) =
        incomingWeight rate rewards C_star C_h u t z := by
  let anchorRead : Z → Fin p.K → ℝ := fun z =>
    (Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextDownView rate rewards C_star C_h u t z hq).elim
      (fun _ => 0) (fun view => view.payload.anchor)
  let weightRead : Z → Fin p.K → ℝ :=
    fun z j => incomingWeight rate rewards C_star C_h u t z j
  have ha : Measurable anchorRead := measurable_anchorRead rate rewards C_star C_h u t control0 hq
  have hw : Measurable weightRead := by
    exact (measurable_of_countable (fun registers : Fin p.K → ℕ × ℕ =>
      fun j => (1 + 1 / (D p : ℝ)) ^ (registers j).1)).comp
      (measurable_fst.comp
        (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
          rate rewards C_star C_h u t))
  have hG : MeasurableSet (G rate rewards C_star C_h u t hq) := by
    simpa only [G] using
      Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.measurableSet_retainedNextDate_ambient rate rewards C_star C_h u t control0 hq
  have hmeas : MeasurableSet {z : Z | z ∈ G rate rewards C_star C_h u t hq →
      anchorRead z = weightRead z} := by
    have heq : {z : Z | z ∈ G rate rewards C_star C_h u t hq →
        anchorRead z = weightRead z} =
        (G rate rewards C_star C_h u t hq)ᶜ ∪ {z | anchorRead z = weightRead z} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]
    rw [heq]
    exact hG.compl.union (measurableSet_eq_fun ha hw)
  have hpair : ∀ᵐ b : B ∂μ,
      b.2 ∈ G rate rewards C_star C_h u t hq →
        anchorRead b.2 = weightRead b.2 := by
    filter_upwards [
      Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.ae_actual_incoming_factor rate rewards C_star C_h u t control0,
      Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_wMinus_eq_renewalAnchor rate rewards C_star C_h u t control0,
      Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalWeightEnvelope.ae_wholeCell_payload_anchor rate rewards C_star C_h u t] with
        b hfactor hweight hpayload
    intro hgate
    have hclear := G_implies_incoming_clear rate rewards C_star C_h u t hq b.2 hgate
    have hGR : b ∈ Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R rate rewards C_star C_h u t control0 := by
      change (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.retainedIncoming rate rewards C_star C_h u t control0 b).overflow = false
      rw [← hfactor.2.1]
      exact hclear
    obtain ⟨view, xi, cell, selected, hview, hparameters, hcell, henabled,
      hrate, hcanonical, hselected, hpayloadSame⟩ :=
        G_actual_readouts rate rewards C_star C_h u t hq b.2 hgate
    obtain ⟨selectedPayload, hselection, hdown, hanchor⟩ := hpayload
    have hselectedEq : selectedPayload = selected := by
      rw [hselection] at hselected
      exact Option.some.inj hselected
    have hviewPayload : view.payload = selectedPayload.view.payload := by
      rw [hselectedEq]
      exact hpayloadSame
    have heq : anchorRead b.2 = weightRead b.2 := by
      funext j
      dsimp only [anchorRead, weightRead]
      rw [Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextDownView, hview]
      simp only [Option.elim_some]
      calc
        view.payload.anchor j = selectedPayload.view.payload.anchor j :=
          congrArg (fun payload => payload.anchor) hviewPayload ▸ rfl
        _ = ReferenceFirstCollectionRenewalComplementMoments.v
            rate rewards C_star C_h u t b j := congrFun hanchor j
        _ = Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus rate rewards C_star C_h u t control0 j b :=
          (hweight hGR j).symm
        _ = incomingWeight rate rewards C_star C_h u t b.2 j := rfl
    exact heq
  have hsource : ∀ᵐ z : Z ∂ν,
      z ∈ G rate rewards C_star C_h u t hq →
        anchorRead z = weightRead z := by
    rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
      rate rewards C_star C_h u t]
    exact (MeasureTheory.ae_map_iff measurable_snd.aemeasurable hmeas).mpr hpair
  filter_upwards [hsource] with z hz
  intro hgate
  exact hz hgate

/-- The actual immediate next-date envelope and its literal canonical
sum-cost bound on the original finite, possibly zero-mass renewal law. -/
theorem ae_G_actual_numerical_weight_envelope
    (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    ∀ᵐ z : Z ∂ν,
      z ∈ G rate rewards C_star C_h u t hq →
        ∃ (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
          (xi : Fin p.K → ℝ) (cell : RecordedQueueRun.RoundInput p.K)
          (selected : ReferenceActivePhysicalStep.Selection
            (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord rate rewards C_star C_h u t z).input),
          (Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator.downView =
            some view ∧
          Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters rate rewards C_star C_h u t z hq = some (true, xi) ∧
          Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq = some cell ∧
          cell.enabled = true ∧ cell.rate = xi ∧
          (∀ j : Fin p.K,
            xi j = CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor j) ∧
          (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord rate rewards C_star C_h u t z).output.preparation.coordinator.selection =
            some selected ∧
          (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord rate rewards C_star C_h u t z).output.preparation.coordinator.downView.map
            (fun sender => sender.payload) = some selected.view.payload ∧
          view.payload = selected.view.payload ∧
          (∀ j : Fin p.K, view.payload.anchor j ≤ w rate rewards C_star C_h u t z j ∧
            w rate rewards C_star C_h u t z j ≤ 2 * view.payload.anchor j) ∧
          (∀ xi' : Fin p.K → ℝ,
            Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters rate rewards C_star C_h u t z hq = some (true, xi') →
            (∑ j : Fin p.K, theta rate rewards C_star C_h u t z j / xi' j) ≤
              CanonicalRecordingRates.R p) := by
  filter_upwards [ae_G_incomingWeight_eq_senderAnchor rate rewards C_star C_h u t control0 hq]
    with z hanchor
  intro hgate
  obtain ⟨view, xi, cell, selected, hview, hparameters, hcell, henabled, hrate,
    hcanonical, hselected, hpayloadSame⟩ :=
      G_actual_readouts rate rewards C_star C_h u t hq z hgate
  have hwholeDown :
      (Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord rate rewards C_star C_h u t z).output.preparation.coordinator.downView.map
        (fun sender => sender.payload) = some selected.view.payload := by
    simp [ReferenceActivePhysicalStep.DispatchCut.downView, hselected]
  have hweight := G_currentWeight_envelope rate rewards C_star C_h u t hq z hgate
  have hweights : ∀ j : Fin p.K,
      view.payload.anchor j ≤ w rate rewards C_star C_h u t z j ∧
        w rate rewards C_star C_h u t z j ≤ 2 * view.payload.anchor j := by
    intro j
    have hEq : incomingWeight rate rewards C_star C_h u t z j = view.payload.anchor j := by
      have hfun := congrFun (hanchor hgate) j
      simp [Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextDownView, hview] at hfun
      exact hfun.symm
    constructor
    · calc
        view.payload.anchor j = incomingWeight rate rewards C_star C_h u t z j := hEq.symm
        _ ≤ w rate rewards C_star C_h u t z j := (hweight j).1
    · calc
        w rate rewards C_star C_h u t z j ≤
            2 * incomingWeight rate rewards C_star C_h u t z j := (hweight j).2
        _ = 2 * view.payload.anchor j := by rw [hEq]
  refine ⟨view, xi, cell, selected, hview, hparameters, hcell, henabled, hrate,
    hcanonical, hselected, hwholeDown, hpayloadSame, hweights, ?_⟩
  intro xi' hparameters'
  have hxi : xi' = xi := by
    have hpair := Option.some.inj (hparameters.symm.trans hparameters')
    exact (Prod.mk.inj hpair).2.symm
  have hxiCanonical : xi' = CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor := by
    rw [hxi]
    exact funext hcanonical
  rw [hxiCanonical]
  simpa only [theta] using
    (CanonicalRecordingRates.sum_theta_div_xi_le_R p rate.eta.property
      view.payload.anchor (w rate rewards C_star C_h u t z)
      view.payload.anchor_pos hweights)

end Bandits.Support.ReferenceFirstCollectionRenewalNextDateNumericalWeightEnvelope

end
