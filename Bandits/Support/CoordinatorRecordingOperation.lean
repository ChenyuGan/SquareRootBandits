/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CompletePublicTable
public import Bandits.Support.RealRewardGridCount
public import Bandits.Support.SnapshotRecordingKernel

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One checked coordinator-local recording operation

This module transcribes the coordinator's physical local recorder on one
selected complete row and one calendar time. It reads only that row's control
slice, the coordinator's own arm and grid-typed observation, and its retained
assignment/confirmation/rate state. The already established snapshot recorder
is used only for the one-slice comparison theorem.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:352-393,398-423`,
`sources/zip4/manuscript/06_interruptions.tex:257-269`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.CoordinatorRecordingOperation

open Bandits.Support.ConstructorDimensions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.SnapshotRecordingKernel
open Bandits.Support.RealRewardGridCount

abbrev Parameters := ConstructorDimensions.Parameters

/-- The coordinator's source-local mode. `confirmationsEmpty` is exactly the
truth value of `P = ∅`; the slow assignment is retained locally. -/
inductive LocalMode (p : Parameters) where
  | collection
  | live (assignment : Assignment p.m p.K) (confirmationsEmpty : Bool)

/-- One local call at a zero-based row index `time : Fin p.T`. Its source
calendar label is `time.val + 1`; the coordinator's own observation is
represented by its actual denominator-`D` grid index. -/
structure Input (p : Parameters) where
  eta : ℝ
  anchor : Fin p.K → ℝ
  currentWeights : Fin p.K → ℝ
  sigma : ℕ
  time : Fin p.T
  gridBoundary : ℕ
  row : CompleteRow p
  ownArm : Fin p.K
  observation : Fin (D p + 1)
  mode : LocalMode p

/-- Runtime parameter and time checks performed before the operation reads a
recording gate or computes a denominator. -/
structure InputsValid {p : Parameters} (input : Input p) : Prop where
  sigma_le_terminal : input.sigma ≤ p.T + 1
  boundary_le_terminal : input.gridBoundary ≤ p.T + 1
  eta_pos : 0 < input.eta
  eta_source_cap : input.eta ≤
    1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ))
  anchor_pos : ∀ j, 0 < input.anchor j
  current_pos : ∀ j, 0 < input.currentWeights j
  anchor_le_current : ∀ j, input.anchor j ≤ input.currentWeights j
  current_le_twice_anchor : ∀ j, input.currentWeights j ≤ 2 * input.anchor j

/-- The local output keeps gate success separate from the raw integer arrival.
Thus a successful thinning gate with zero floor remains distinguishable from
gate failure. The dependent bound is the checked output-domain condition. -/
structure Output (p : Parameters) where
  gateArm : Option (Fin p.K)
  rawArrival : ℕ
  rawArrival_le_D : rawArrival ≤ D p

/-- The ordinary no-arrival output. -/
def zeroOutput (p : Parameters) : Output p :=
  ⟨none, 0, Nat.zero_le _⟩

/-- The source DATA selector from the current row's own continuous slice. -/
def selectedSlot {p : Parameters} (input : Input p) : Slot :=
  slotFromScalar (coordinate Label.slot
    (sliceAt input.time input.row.2))

/-- The recorder source selected by this same row slice. -/
def selectedRecorder {p : Parameters} (input : Input p) : Fin p.m :=
  recorderSourceFromScalar p.two_le_m
    (coordinate Label.rec (sliceAt input.time input.row.2))

/-- The manuscript's one-based source round represented by a zero-based
calendar index in `Fin p.T`. -/
def sourceCalendarRound {p : Parameters} (input : Input p) : ℕ :=
  input.time.val + 1

/-- The source freeze condition. `sigma` and `gridBoundary` are one-based
manuscript round labels, so the zero-based `Fin p.T` index is converted by
`sourceCalendarRound` before comparing it with the boundary. -/
def isFrozen {p : Parameters} (input : Input p) : Prop :=
  0 < input.sigma ∧ sourceCalendarRound input ≥ input.gridBoundary

/-- A finite calendar index represents an in-horizon one-based source round. -/
theorem sourceCalendarRound_le_horizon {p : Parameters} (input : Input p) :
    sourceCalendarRound input ≤ p.T := by
  simpa only [sourceCalendarRound, Nat.succ_eq_add_one] using
    Nat.succ_le_of_lt input.time.isLt

/-- Every source round `g` in `1,...,T` is represented by its zero-based
calendar index `g-1` in `Fin p.T`. -/
theorem exists_calendar_index_for_source_round {p : Parameters} (g : ℕ)
    (hg_pos : 0 < g) (hg_le : g ≤ p.T) :
    ∃ time : Fin p.T, time.val + 1 = g := by
  have hround : g - 1 + 1 = g := by omega
  exact ⟨⟨g - 1, by omega⟩, hround⟩

/-- If the source round is the stored boundary `g`, the coordinator is
frozen on that round, as required by the inclusive source test `t ≥ g`. -/
theorem isFrozen_at_source_boundary {p : Parameters} (input : Input p)
    (hsigma : 0 < input.sigma)
    (hround : sourceCalendarRound input = input.gridBoundary) :
    isFrozen input := by
  exact ⟨hsigma, hround ▸ le_rfl⟩

/-- The round immediately before a boundary is not frozen by that boundary
test. This case can occur only when the preceding source round is in `Fin p.T`.
-/
theorem not_isFrozen_at_preceding_source_round {p : Parameters}
    (input : Input p)
    (hround : sourceCalendarRound input + 1 = input.gridBoundary) :
    ¬ isFrozen input := by
  intro hfrozen
  have hlt : sourceCalendarRound input < input.gridBoundary := by omega
  exact (not_le_of_gt hlt) hfrozen.2

/-- Source label `T+1` is the out-of-horizon sentinel and is never represented
by a `Fin p.T` calendar index. -/
theorem sourceCalendarRound_ne_terminal {p : Parameters} (input : Input p) :
    sourceCalendarRound input ≠ p.T + 1 := by
  have hround := sourceCalendarRound_le_horizon input
  omega

/-- The initial terminal boundary `g=T+1` is never reached by a finite source
round, so it cannot freeze the coordinator within the horizon. -/
theorem not_isFrozen_at_terminal_boundary {p : Parameters} (input : Input p)
    (hboundary : input.gridBoundary = p.T + 1) :
    ¬ isFrozen input := by
  intro hfrozen
  have hround := sourceCalendarRound_le_horizon input
  have hfreeze : sourceCalendarRound input ≥ input.gridBoundary := hfrozen.2
  rw [hboundary] at hfreeze
  omega

/-- The coordinator owns every collection arm and the fast complement of its
live retained assignment. -/
def ownsArm {p : Parameters} (mode : LocalMode p) (j : Fin p.K) : Prop :=
  match mode with
  | .collection => True
  | .live assignment _ => j ∉ (assignmentSlowSet p assignment).val

/-- The coordinator's DATA action probability at arm `j`: it is `1/K` in
collection or while confirmations are missing, and `qΓ` on the fast
complement once all confirmations are present. Outside that complement the
literal action probability is zero. -/
def coordinatorArmProbability {p : Parameters} (input : Input p)
    (hvalid : InputsValid input) : ℝ :=
  match input.mode with
  | .collection => 1 / (p.K : ℝ)
  | .live _ false => 1 / (p.K : ℝ)
  | .live assignment true =>
      if hj : input.ownArm ∈ fastArmFinset (assignmentSlowSet p assignment) then
        qGamma p input.eta hvalid.eta_pos hvalid.eta_source_cap
          input.anchor input.currentWeights hvalid.anchor_pos hvalid.current_pos
          hvalid.anchor_le_current hvalid.current_le_twice_anchor
          (assignmentSlowSet p assignment) ⟨input.ownArm, hj⟩
      else
        0

/-- The literal one-round DATA/source/action/mask mass before thinning, with
the two source factors both equal to `1/2`. -/
def coordinatorRawGateMass {p : Parameters} (input : Input p)
    (hvalid : InputsValid input) : ℝ :=
  (1 / 2) * (1 / 2) * coordinatorArmProbability input hvalid *
    recordingZeta p.m p.K

/-- The canonical inclusive thinning threshold for the supplied arm. -/
def coordinatorThreshold {p : Parameters} (input : Input p)
    (hvalid : InputsValid input) : ℝ :=
  xi p input.eta input.anchor input.ownArm / coordinatorRawGateMass input hvalid

/-- The coordinator's own source mask, read from all the other players'
public pilot fields in this row slice. -/
def ownMaskPasses {p : Parameters} (input : Input p) : Prop :=
  recordingMask (K_pos p) (coordinator p.two_le_m) input.ownArm
    (sliceAt input.time input.row.2)

/-- The unthinned integer floor for this observation and actual arm. -/
def floorArrival {p : Parameters} (input : Input p) : ℕ :=
  Nat.floor (((D p : ℝ) * input.eta *
    realRewardGridValue (D p) (D_pos p) input.observation) /
      xi p input.eta input.anchor input.ownArm)

/-- The checked local computation. Every invalid input, denominator, Bernoulli
parameter, or output-domain result returns `none` before an output is stored.
Ordinary recording is independent of any analysis-overflow state. -/
def executeValid {p : Parameters} (input : Input p)
    (hvalid : InputsValid input) : Option (Output p) := by
  classical
  by_cases hdata : selectedSlot input = dataSlot
  · by_cases hsource : selectedRecorder input = coordinator p.two_le_m
    · by_cases hfrozen : isFrozen input
      · exact some (zeroOutput p)
      · by_cases howns : ownsArm input.mode input.ownArm
        · by_cases hmask : ownMaskPasses input
          · let raw := coordinatorRawGateMass input hvalid
            if hden : 0 < raw then
              let threshold := xi p input.eta input.anchor input.ownArm / raw
              if hparameter : threshold ∈ Set.Icc (0 : ℝ) 1 then
                if hthin : (coordinate Label.thin
                    (sliceAt input.time input.row.2)).val ≤ threshold then
                  let arrival := floorArrival input
                  if houtput : arrival ≤ D p then
                    exact some ⟨some input.ownArm, arrival, houtput⟩
                  else
                    exact none
                else
                  exact some (zeroOutput p)
              else
                exact none
            else
              exact none
          · exact some (zeroOutput p)
        · exact some (zeroOutput p)
    · exact some (zeroOutput p)
  · exact some (zeroOutput p)

/-- Total checked coordinator-local recorder operation. -/
def run {p : Parameters} (input : Input p) : Option (Output p) := by
  classical
  by_cases hvalid : InputsValid input
  · exact executeValid input hvalid
  · exact none

/-- The value carried by the typed quantized observation. -/
def observationValue {p : Parameters} (input : Input p) : ℝ :=
  realRewardGridValue (D p) (D_pos p) input.observation

/-- The same retained local input with only the coordinator's typed own
observation replaced. In particular the row, arm, mode, rates, weights,
calendar index, and boundary are unchanged. -/
def withObservation {p : Parameters} (input : Input p)
    (observation : Fin (D p + 1)) : Input p :=
  { input with observation := observation }

/-- Input-domain validity is independent of the own observation value. -/
theorem inputsValid_withObservation {p : Parameters} (input : Input p)
    (hvalid : InputsValid input) (observation : Fin (D p + 1)) :
    InputsValid (withObservation input observation) := by
  exact ⟨hvalid.sigma_le_terminal, hvalid.boundary_le_terminal,
    hvalid.eta_pos, hvalid.eta_source_cap, hvalid.anchor_pos,
    hvalid.current_pos, hvalid.anchor_le_current,
    hvalid.current_le_twice_anchor⟩

/-- The source raw arrival is exactly the literal floor of the coordinator's
own typed feedback value. -/
theorem floorArrival_eq_literal {p : Parameters} (input : Input p) :
    floorArrival input = Nat.floor
      ((D p : ℝ) * input.eta * observationValue input /
        xi p input.eta input.anchor input.ownArm) := by
  rfl

/-- The three regime formulas for the coordinator's own play probability. -/
theorem coordinatorArmProbability_collection {p : Parameters}
    (input : Input p) (hvalid : InputsValid input)
    (hmode : input.mode = .collection) :
    coordinatorArmProbability input hvalid = 1 / (p.K : ℝ) := by
  simp [coordinatorArmProbability, hmode]

theorem coordinatorArmProbability_live_confirmations_missing {p : Parameters}
    (input : Input p) (hvalid : InputsValid input)
    (assignment : Assignment p.m p.K)
    (hmode : input.mode = .live assignment false) :
    coordinatorArmProbability input hvalid = 1 / (p.K : ℝ) := by
  simp [coordinatorArmProbability, hmode]

theorem coordinatorArmProbability_live_confirmed {p : Parameters}
    (input : Input p) (hvalid : InputsValid input)
    (assignment : Assignment p.m p.K)
    (hmode : input.mode = .live assignment true)
    (hfast : input.ownArm ∈
      fastArmFinset (assignmentSlowSet p assignment)) :
    coordinatorArmProbability input hvalid =
      qGamma p input.eta hvalid.eta_pos hvalid.eta_source_cap
        input.anchor input.currentWeights hvalid.anchor_pos hvalid.current_pos
        hvalid.anchor_le_current hvalid.current_le_twice_anchor
        (assignmentSlowSet p assignment) ⟨input.ownArm, hfast⟩ := by
  simp [coordinatorArmProbability, hmode, hfast]

/-- The source cap and accepted fast-marginal feasibility make the local raw
gate denominator positive and at least its canonical recording rate whenever
the coordinator owns the supplied arm. -/
theorem rawGateMass_feasible {p : Parameters} (input : Input p)
    (hvalid : InputsValid input) (howns : ownsArm input.mode input.ownArm) :
    0 < coordinatorRawGateMass input hvalid ∧
      xi p input.eta input.anchor input.ownArm ≤
        coordinatorRawGateMass input hvalid := by
  have hxi := xi_pos p hvalid.eta_pos input.anchor input.ownArm
  cases hmode : input.mode with
  | collection =>
      have hbounds := canonical_recording_rate_raw_gate_bounds p
        hvalid.eta_pos hvalid.eta_source_cap input.anchor hvalid.anchor_pos
        (coordinator p.two_le_m) input.ownArm
      have hraw : coordinatorRawGateMass input hvalid =
          pilotRecordingGateRawProbability (K := p.K)
            (coordinator p.two_le_m) := by
        simp only [coordinatorRawGateMass, coordinatorArmProbability, hmode,
          pilotRecordingGateRawProbability]
        rw [ActiveRoundActions.coordinator, recorderMass_coordinator p.two_le_m]
      rw [hraw]
      exact ⟨hxi.trans_le hbounds.2.2.1,
        hbounds.2.2.1⟩
  | live assignment confirmationsEmpty =>
      cases confirmationsEmpty with
      | false =>
          have hbounds := canonical_recording_rate_raw_gate_bounds p
            hvalid.eta_pos hvalid.eta_source_cap input.anchor hvalid.anchor_pos
            (coordinator p.two_le_m) input.ownArm
          have hraw : coordinatorRawGateMass input hvalid =
              pilotRecordingGateRawProbability (K := p.K)
                (coordinator p.two_le_m) := by
            simp only [coordinatorRawGateMass, coordinatorArmProbability, hmode,
              pilotRecordingGateRawProbability]
            rw [ActiveRoundActions.coordinator, recorderMass_coordinator p.two_le_m]
          rw [hraw]
          exact ⟨hxi.trans_le hbounds.2.2.1,
            hbounds.2.2.1⟩
      | true =>
          have hfast : input.ownArm ∈
              fastArmFinset (assignmentSlowSet p assignment) := by
            simpa [ownsArm, hmode] using howns
          let fast : FastArm (assignmentSlowSet p assignment) :=
            ⟨input.ownArm, hfast⟩
          have hq := qGamma_ge_16_xi p hvalid.eta_pos
            hvalid.eta_source_cap input.anchor input.currentWeights
            hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
            hvalid.current_le_twice_anchor (assignmentSlowSet p assignment) fast
          have hz := recordingZeta_gt_quarter p.two_le_m p.m_lt_K
          have hraw : coordinatorRawGateMass input hvalid =
              (1 / 2) * (1 / 2) *
                qGamma p input.eta hvalid.eta_pos hvalid.eta_source_cap
                  input.anchor input.currentWeights hvalid.anchor_pos
                  hvalid.current_pos hvalid.anchor_le_current
                  hvalid.current_le_twice_anchor
                  (assignmentSlowSet p assignment) fast *
                recordingZeta p.m p.K := by
            simp [coordinatorRawGateMass, coordinatorArmProbability, hmode,
              hfast, fast]
          rw [hraw]
          change 16 * xi p input.eta input.anchor input.ownArm ≤ _ at hq
          have hq' : xi p input.eta input.anchor input.ownArm ≤
              qGamma p input.eta hvalid.eta_pos hvalid.eta_source_cap
                input.anchor input.currentWeights hvalid.anchor_pos hvalid.current_pos
                hvalid.anchor_le_current hvalid.current_le_twice_anchor
                (assignmentSlowSet p assignment) fast := by
            nlinarith [hxi, hq]
          have hzpos : 0 < recordingZeta p.m p.K :=
            lt_trans (by norm_num) hz
          have hmul := mul_le_mul_of_nonneg_right hq
            (le_of_lt hzpos)
          have hfour : 4 * xi p input.eta input.anchor input.ownArm ≤
              16 * xi p input.eta input.anchor input.ownArm *
                recordingZeta p.m p.K := by
            calc
              4 * xi p input.eta input.anchor input.ownArm =
                  16 * xi p input.eta input.anchor input.ownArm * (1 / 4) := by ring
              _ ≤ 16 * xi p input.eta input.anchor input.ownArm *
                    recordingZeta p.m p.K :=
                mul_le_mul_of_nonneg_left hz.le (by positivity)
          have hprod : 4 * xi p input.eta input.anchor input.ownArm ≤
              qGamma p input.eta hvalid.eta_pos hvalid.eta_source_cap
                input.anchor input.currentWeights hvalid.anchor_pos hvalid.current_pos
                hvalid.anchor_le_current hvalid.current_le_twice_anchor
                (assignmentSlowSet p assignment) fast *
                recordingZeta p.m p.K := hfour.trans hmul
          have hqpos : 0 <
              qGamma p input.eta hvalid.eta_pos hvalid.eta_source_cap
                input.anchor input.currentWeights hvalid.anchor_pos hvalid.current_pos
                hvalid.anchor_le_current hvalid.current_le_twice_anchor
                (assignmentSlowSet p assignment) fast := hxi.trans_le hq'
          constructor
          · positivity
          · nlinarith [hprod]

/-- The source cap and `ξ ≥ 32η` imply the checked raw arrival lies in
`[0,D]` for every typed quantized observation. -/
theorem floorArrival_le_D {p : Parameters} (input : Input p)
    (hvalid : InputsValid input) : floorArrival input ≤ D p := by
  have hxi : 0 < xi p input.eta input.anchor input.ownArm :=
    xi_pos p hvalid.eta_pos input.anchor input.ownArm
  have h32 := thirtyTwo_mul_eta_le_xi p hvalid.eta_pos
    input.anchor input.ownArm
  have heta_xi : input.eta ≤ xi p input.eta input.anchor input.ownArm := by
    nlinarith [hvalid.eta_pos]
  have hy := realRewardGridValue_mem_Icc (D p) (D_pos p) input.observation
  have heta_y : input.eta * observationValue input ≤
      xi p input.eta input.anchor input.ownArm := by
    calc
      input.eta * observationValue input ≤ input.eta :=
        mul_le_of_le_one_right hvalid.eta_pos.le hy.2
      _ ≤ xi p input.eta input.anchor input.ownArm := heta_xi
  have hnum : (D p : ℝ) * input.eta * observationValue input ≤
      (D p : ℝ) * xi p input.eta input.anchor input.ownArm := by
    calc
      (D p : ℝ) * input.eta * observationValue input =
          (D p : ℝ) * (input.eta * observationValue input) := by ring
      _ ≤ (D p : ℝ) * xi p input.eta input.anchor input.ownArm :=
        mul_le_mul_of_nonneg_left heta_y (Nat.cast_nonneg _)
  have hdiv :
      ((D p : ℝ) * input.eta * observationValue input) /
        xi p input.eta input.anchor input.ownArm ≤ (D p : ℝ) := by
    apply (div_le_iff₀ hxi).2
    simpa [mul_comm] using hnum
  have harg_nonneg : 0 ≤
      ((D p : ℝ) * input.eta * observationValue input) /
        xi p input.eta input.anchor input.ownArm :=
    div_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg (D p)) hvalid.eta_pos.le) hy.1)
      hxi.le
  have hfloor :
      (Nat.floor (((D p : ℝ) * input.eta * observationValue input) /
        xi p input.eta input.anchor input.ownArm) : ℝ) ≤
          ((D p : ℝ) * input.eta * observationValue input) /
            xi p input.eta input.anchor input.ownArm := Nat.floor_le harg_nonneg
  have hcast : (floorArrival input : ℝ) ≤ (D p : ℝ) := by
    exact hfloor.trans (by simpa [floorArrival, observationValue] using hdiv)
  exact_mod_cast hcast

/-- An owned arm always has a valid source thinning parameter. This derives
denominator positivity and `thinning ≤ 1` from the accepted canonical
feasibility APIs, including `qΓ ≥ 16ξ` on the confirmed fast branch. -/
theorem coordinatorThreshold_mem_Icc_of_owned {p : Parameters}
    (input : Input p) (hvalid : InputsValid input)
    (howns : ownsArm input.mode input.ownArm) :
    coordinatorThreshold input hvalid ∈ Set.Icc (0 : ℝ) 1 := by
  have hxi := xi_pos p hvalid.eta_pos input.anchor input.ownArm
  rcases rawGateMass_feasible input hvalid howns with ⟨hrawpos, hraw⟩
  exact ⟨div_nonneg hxi.le hrawpos.le, (div_le_one₀ hrawpos).2 hraw⟩

/-- Changing only the coordinator's typed own observation cannot change the
gate-arm channel. A successful gate remains distinguishable from failure
even when either observation's literal floor is zero. -/
theorem executeValid_gateArm_eq_of_observation_change {p : Parameters}
    (input : Input p) (hvalid : InputsValid input)
    (observation : Fin (D p + 1)) :
    (executeValid input hvalid).map Output.gateArm =
      (executeValid (withObservation input observation)
        (inputsValid_withObservation input hvalid observation)).map Output.gateArm := by
  have hfloor := floorArrival_le_D input hvalid
  have hvalid' := inputsValid_withObservation input hvalid observation
  let input' := withObservation input observation
  have hfloor' := floorArrival_le_D input' hvalid'
  have hdata : selectedSlot input = selectedSlot input' := by
    simp [input', withObservation, selectedSlot]
  have hsource : selectedRecorder input = selectedRecorder input' := by
    simp [input', withObservation, selectedRecorder]
  have hfrozen : isFrozen input = isFrozen input' := by
    simp [input', withObservation, isFrozen, sourceCalendarRound]
  have howns : ownsArm input.mode input.ownArm =
      ownsArm input'.mode input'.ownArm := by
    simp [input', withObservation]
  have hmask : ownMaskPasses input = ownMaskPasses input' := by
    simp [input', withObservation, ownMaskPasses]
  have harm : input.ownArm = input'.ownArm := by
    simp [input', withObservation]
  have hthin : coordinate Label.thin (sliceAt input.time input.row.2) =
      coordinate Label.thin (sliceAt input'.time input'.row.2) := by
    simp [input', withObservation]
  have hraw : coordinatorRawGateMass input hvalid =
      coordinatorRawGateMass input' hvalid' := by
    simp [coordinatorRawGateMass, coordinatorArmProbability, input',
      withObservation]
  have hxi : xi p input.eta input.anchor input.ownArm =
      xi p input'.eta input'.anchor input'.ownArm := by
    simp [input', withObservation]
  change (executeValid input hvalid).map Output.gateArm =
    (executeValid input' hvalid').map Output.gateArm
  simp only [executeValid]
  rw [hdata, hsource, hfrozen, howns, hmask, hraw, hxi, harm, hthin]
  simp only [Option.map]
  split_ifs <;> simp

/-- The total checked operation has the same gate-arm result after replacing
only the coordinator's typed own observation. The raw arrival is governed
separately by `floorArrival_eq_literal` on successful gates. -/
theorem run_gateArm_eq_of_observation_change {p : Parameters}
    (input : Input p) (hvalid : InputsValid input)
    (observation : Fin (D p + 1)) :
    (run input).map Output.gateArm =
      (run (withObservation input observation)).map Output.gateArm := by
  have hvalid' := inputsValid_withObservation input hvalid observation
  simpa [run, hvalid, hvalid'] using
    executeValid_gateArm_eq_of_observation_change input hvalid observation

/-- The checked wrapper rejects every invalid time or rate/weight input. -/
theorem run_none_of_invalid {p : Parameters} (input : Input p)
    (hinvalid : ¬ InputsValid input) : run input = none := by
  simp [run, hinvalid]

/-- A valid non-DATA row returns the initialized zero arrival. -/
theorem executeValid_zero_of_not_data {p : Parameters} (input : Input p)
    (hvalid : InputsValid input)
    (hdata : selectedSlot input ≠ dataSlot) :
    executeValid input hvalid = some (zeroOutput p) := by
  simp [executeValid, hdata]

/-- A valid row recorded by another public source has no coordinator-local
gate or arrival. This says nothing about that other source's global outcome. -/
theorem executeValid_zero_of_other_source {p : Parameters} (input : Input p)
    (hvalid : InputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input ≠ coordinator p.two_le_m) :
    executeValid input hvalid = some (zeroOutput p) := by
  simp [executeValid, hdata, hsource]

/-- A valid frozen coordinator stops before the ownership, mask, or thinning
tests. -/
theorem executeValid_zero_of_frozen {p : Parameters} (input : Input p)
    (hvalid : InputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hfrozen : isFrozen input) :
    executeValid input hvalid = some (zeroOutput p) := by
  simp [executeValid, hdata, hsource, hfrozen]

/-- Live coordinator arms in the retained slow set are not locally owned. -/
theorem executeValid_zero_of_unowned {p : Parameters} (input : Input p)
    (hvalid : InputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotfrozen : ¬ isFrozen input)
    (howns : ¬ ownsArm input.mode input.ownArm) :
    executeValid input hvalid = some (zeroOutput p) := by
  simp [executeValid, hdata, hsource, hnotfrozen, howns]

/-- An owned coordinator arm rejected by the public-row mask keeps the
initialized zero output. -/
theorem executeValid_zero_of_mask_rejected {p : Parameters} (input : Input p)
    (hvalid : InputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotfrozen : ¬ isFrozen input)
    (howns : ownsArm input.mode input.ownArm)
    (hmask : ¬ ownMaskPasses input) :
    executeValid input hvalid = some (zeroOutput p) := by
  simp [executeValid, hdata, hsource, hnotfrozen, howns, hmask]

/-- The inclusive local thinning comparison succeeds at equality. -/
theorem executeValid_recorded_of_gate {p : Parameters} (input : Input p)
    (hvalid : InputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotfrozen : ¬ isFrozen input)
    (howns : ownsArm input.mode input.ownArm)
    (hmask : ownMaskPasses input)
    (hthin : (coordinate Label.thin
      (sliceAt input.time input.row.2)).val ≤ coordinatorThreshold input hvalid)
    :
    executeValid input hvalid =
      some ⟨some input.ownArm, floorArrival input, floorArrival_le_D input hvalid⟩ := by
  have hden := (rawGateMass_feasible input hvalid howns).1
  have hparameter := coordinatorThreshold_mem_Icc_of_owned input hvalid howns
  have hparameter' :
      xi p input.eta input.anchor input.ownArm /
        coordinatorRawGateMass input hvalid ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [coordinatorThreshold] using hparameter
  have hthin' : (coordinate Label.thin
      (sliceAt input.time input.row.2)).val ≤
        xi p input.eta input.anchor input.ownArm /
          coordinatorRawGateMass input hvalid := by
    simpa [coordinatorThreshold] using hthin
  have houtput := floorArrival_le_D input hvalid
  simp [executeValid, hdata, hsource, hnotfrozen, howns, hmask,
    hden, hparameter', hthin', houtput]

/-- A valid owned arm whose thinning scalar exceeds its accepted canonical
threshold keeps the initialized zero output. Positivity and the parameter
upper bound are derived from the canonical local rate APIs. -/
theorem executeValid_zero_of_thinning_rejected {p : Parameters}
    (input : Input p) (hvalid : InputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotfrozen : ¬ isFrozen input)
    (howns : ownsArm input.mode input.ownArm)
    (hmask : ownMaskPasses input)
    (hthin : ¬ ((coordinate Label.thin
      (sliceAt input.time input.row.2)).val ≤ coordinatorThreshold input hvalid)) :
    executeValid input hvalid = some (zeroOutput p) := by
  have hden := (rawGateMass_feasible input hvalid howns).1
  have hparameter := coordinatorThreshold_mem_Icc_of_owned input hvalid howns
  have hparameter' :
      xi p input.eta input.anchor input.ownArm /
        coordinatorRawGateMass input hvalid ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [coordinatorThreshold] using hparameter
  have hthin' : ¬ ((coordinate Label.thin
      (sliceAt input.time input.row.2)).val ≤
        xi p input.eta input.anchor input.ownArm /
          coordinatorRawGateMass input hvalid) := by
    simpa [coordinatorThreshold] using hthin
  simp [executeValid, hdata, hsource, hnotfrozen, howns, hmask,
    hden, hparameter', hthin']

/-- On a successful gate the stored natural is exactly the literal source
floor, including the value zero. -/
theorem executeValid_gate_and_floor {p : Parameters} (input : Input p)
    (hvalid : InputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotfrozen : ¬ isFrozen input)
    (howns : ownsArm input.mode input.ownArm)
    (hmask : ownMaskPasses input)
    (hthin : (coordinate Label.thin
      (sliceAt input.time input.row.2)).val ≤ coordinatorThreshold input hvalid) :
    ∃ out, executeValid input hvalid = some out ∧
      out.gateArm = some input.ownArm ∧ out.rawArrival = floorArrival input := by
  refine ⟨⟨some input.ownArm, floorArrival input, floorArrival_le_D input hvalid⟩,
    executeValid_recorded_of_gate input hvalid hdata hsource hnotfrozen
      howns hmask hthin, rfl, rfl⟩

/-- A successful gate whose literal floor is zero still returns its arm in the
gate channel and zero separately as the raw arrival. -/
theorem executeValid_gate_with_zero_floor {p : Parameters} (input : Input p)
    (hvalid : InputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotfrozen : ¬ isFrozen input)
    (howns : ownsArm input.mode input.ownArm)
    (hmask : ownMaskPasses input)
    (hthin : (coordinate Label.thin
      (sliceAt input.time input.row.2)).val ≤ coordinatorThreshold input hvalid)
    (hfloor : floorArrival input = 0) :
    ∃ out, executeValid input hvalid = some out ∧
      out.gateArm = some input.ownArm ∧ out.rawArrival = 0 := by
  obtain ⟨out, hout, hgate, harrival⟩ := executeValid_gate_and_floor
    input hvalid hdata hsource hnotfrozen howns hmask hthin
  exact ⟨out, hout, hgate, by rw [harrival, hfloor]⟩

/-- If the arm, rate data, and observed scalar agree, the corresponding raw
floors agree. Gate-arm invariance under changing only the own observation is
stated separately by `run_gateArm_eq_of_observation_change`; this result does
not assert that different feedback values have the same raw arrival. -/
theorem floorArrival_eq_of_observation_eq {p : Parameters}
    (input input' : Input p) (heta : input.eta = input'.eta)
    (hanchor : input.anchor = input'.anchor)
    (harm : input.ownArm = input'.ownArm)
    (hobs : observationValue input = observationValue input') :
    floorArrival input = floorArrival input' := by
  unfold observationValue at hobs
  unfold floorArrival
  rw [heta, hanchor, harm, hobs]

/-- The coordinator-source projection of the existing collection analysis map
on the same public-row slice `sliceAt input.time input.row.2`, representing
source round `sourceCalendarRound input`. When the row selects another
recorder, this projection is `none`; the full global map may still contain
that other player's outcome. -/
def collectionCoordinatorSourceMapPart {p : Parameters} (input : Input p)
    (hvalid : InputsValid input) (enabled : Bool) : Option (Fin p.K) :=
  if selectedRecorder input = coordinator p.two_le_m then
    SnapshotRecordingKernel.recordingMap p .collection enabled input.eta
      hvalid.eta_pos hvalid.eta_source_cap input.anchor input.currentWeights
      hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
      hvalid.current_le_twice_anchor (sliceAt input.time input.row.2)
  else
    none

/-- The coordinator-source projection of the existing collection physical
increment on the same source-calendar slice. It is explicitly zero when
another player is the recorder. -/
def collectionCoordinatorSourceIncrement {p : Parameters} (input : Input p)
    (hvalid : InputsValid input) (enabled : Bool)
    (rewardRow : RewardRow p.K) : ℕ :=
  if selectedRecorder input = coordinator p.two_le_m then
    SnapshotRecordingKernel.collectionPhysicalIncrement p input.eta
      hvalid.eta_pos hvalid.eta_source_cap input.anchor input.currentWeights
      hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
      hvalid.current_le_twice_anchor enabled (sliceAt input.time input.row.2)
      rewardRow
  else
    0

/-- The coordinator-source projection of the existing live arm map on the
same source-calendar slice. It is `none` when the row selected a follower
recorder. -/
def liveCoordinatorSourceMapPart {p : Parameters} (input : Input p)
    (hvalid : InputsValid input) (assignment : Assignment p.m p.K)
    (snapshot : Snapshot assignment) (enabled : Bool) : Option (Fin p.K) :=
  if selectedRecorder input = coordinator p.two_le_m then
    SnapshotRecordingKernel.recordingMap p (.live assignment snapshot) enabled
      input.eta hvalid.eta_pos hvalid.eta_source_cap input.anchor
      input.currentWeights hvalid.anchor_pos hvalid.current_pos
      hvalid.anchor_le_current hvalid.current_le_twice_anchor
      (sliceAt input.time input.row.2)
  else
    none

/-- The coordinator-source projection of the existing live physical raw
increment on the same source-calendar slice. The selected follower's physical
increment is not attributed to the coordinator. -/
def liveCoordinatorSourceIncrement {p : Parameters} (input : Input p)
    (hvalid : InputsValid input) (assignment : Assignment p.m p.K)
    (snapshot : Snapshot assignment) {B : ℕ}
    (down up : HashedWord B) (enabled : Bool)
    (rewardRow : RewardRow p.K) : ℕ :=
  if selectedRecorder input = coordinator p.two_le_m then
    SnapshotRecordingKernel.livePhysicalIncrement p input.eta
      hvalid.eta_pos hvalid.eta_source_cap input.anchor input.currentWeights
      hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
      hvalid.current_le_twice_anchor assignment snapshot down up enabled
      (sliceAt input.time input.row.2) rewardRow
  else
    0

/-- In a coordinator-source collection call, the literal local raw-gate mass
is exactly the raw mass already used by the snapshot recording kernel. -/
theorem collectionRawGateMass_eq_snapshot {p : Parameters}
    (input : Input p) (hvalid : InputsValid input)
    (hmode : input.mode = .collection) :
    coordinatorRawGateMass input hvalid =
      SnapshotRecordingKernel.rawGateMass p .collection input.eta
        hvalid.eta_pos hvalid.eta_source_cap input.anchor input.currentWeights
        hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
        hvalid.current_le_twice_anchor (coordinator p.two_le_m) input.ownArm := by
  simp only [coordinatorRawGateMass, coordinatorArmProbability, hmode,
    SnapshotRecordingKernel.rawGateMass,
    SnapshotRecordingKernel.actionProbability]
  rw [ActiveRoundActions.coordinator, recorderMass_coordinator p.two_le_m]

/-- Consequently the local collection threshold is the accepted snapshot
kernel threshold, with the same DATA, coordinator-source and mask scalars. -/
theorem collectionThreshold_eq_snapshot {p : Parameters}
    (input : Input p) (hvalid : InputsValid input)
    (hmode : input.mode = .collection) :
    coordinatorThreshold input hvalid =
      SnapshotRecordingKernel.thinningThreshold p .collection input.eta
        hvalid.eta_pos hvalid.eta_source_cap input.anchor input.currentWeights
        hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
        hvalid.current_le_twice_anchor (coordinator p.two_le_m) input.ownArm := by
  unfold coordinatorThreshold SnapshotRecordingKernel.thinningThreshold
  rw [collectionRawGateMass_eq_snapshot input hvalid hmode]

/-- On a fixed live assignment snapshot, the local coordinator probability is
the existing snapshot action probability for either value of `P = ∅`. -/
theorem liveRawGateMass_eq_snapshot {p : Parameters} (input : Input p)
    (hvalid : InputsValid input) (assignment : Assignment p.m p.K)
    (confirmationsEmpty : Bool) (snapshot : Snapshot assignment)
    (hmode : input.mode = .live assignment confirmationsEmpty)
    (hmissing : snapshot.missing = ∅ ↔ confirmationsEmpty = true) :
    coordinatorRawGateMass input hvalid =
      SnapshotRecordingKernel.rawGateMass p (.live assignment snapshot)
        input.eta hvalid.eta_pos hvalid.eta_source_cap input.anchor
        input.currentWeights hvalid.anchor_pos hvalid.current_pos
        hvalid.anchor_le_current hvalid.current_le_twice_anchor
        (coordinator p.two_le_m) input.ownArm := by
  have hprob : coordinatorArmProbability input hvalid =
      SnapshotRecordingKernel.actionProbability p (.live assignment snapshot)
        input.eta hvalid.eta_pos hvalid.eta_source_cap input.anchor
        input.currentWeights hvalid.anchor_pos hvalid.current_pos
        hvalid.anchor_le_current hvalid.current_le_twice_anchor
        (coordinator p.two_le_m) input.ownArm := by
    cases confirmationsEmpty with
    | false =>
        have hnonempty : snapshot.missing ≠ ∅ := by
          intro hempty
          have hfalse : false = true := hmissing.mp hempty
          cases hfalse
        simp [coordinatorArmProbability, hmode,
          SnapshotRecordingKernel.actionProbability, hnonempty]
    | true =>
        have hempty : snapshot.missing = ∅ := hmissing.mpr rfl
        simp [coordinatorArmProbability, hmode,
          SnapshotRecordingKernel.actionProbability, hempty]
  unfold coordinatorRawGateMass SnapshotRecordingKernel.rawGateMass
  rw [hprob, ActiveRoundActions.coordinator, recorderMass_coordinator p.two_le_m]

/-- The local live threshold equals the snapshot-kernel threshold, including
the pilot threshold while confirmations remain and `qΓ` on the fast
complement after they clear. -/
theorem liveThreshold_eq_snapshot {p : Parameters} (input : Input p)
    (hvalid : InputsValid input) (assignment : Assignment p.m p.K)
    (confirmationsEmpty : Bool) (snapshot : Snapshot assignment)
    (hmode : input.mode = .live assignment confirmationsEmpty)
    (hmissing : snapshot.missing = ∅ ↔ confirmationsEmpty = true) :
    coordinatorThreshold input hvalid =
      SnapshotRecordingKernel.thinningThreshold p (.live assignment snapshot)
        input.eta hvalid.eta_pos hvalid.eta_source_cap input.anchor
        input.currentWeights hvalid.anchor_pos hvalid.current_pos
        hvalid.anchor_le_current hvalid.current_le_twice_anchor
        (coordinator p.two_le_m) input.ownArm := by
  unfold coordinatorThreshold SnapshotRecordingKernel.thinningThreshold
  rw [liveRawGateMass_eq_snapshot input hvalid assignment confirmationsEmpty
    snapshot hmode hmissing]

/-- A conditional one-slice collection comparison. The local operation and
snapshot kernel use the identical public-row slice at `sourceCalendarRound
input`. If the supplied arm and grid observation are the accepted physical
pilot action and feedback, a successful local gate is exactly the
coordinator-source atom of `recordingMap`, and its arrival is the projected
`collectionPhysicalIncrement`. -/
theorem collection_coordinator_recording_agrees {p : Parameters}
    (input : Input p) (hvalid : InputsValid input)
    (rewardRow : RewardRow p.K)
    (hmode : input.mode = .collection)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotfrozen : ¬ isFrozen input)
    (harm : input.ownArm = pilotDraw (K_pos p)
      (coordinator p.two_le_m) (sliceAt input.time input.row.2))
    (hmask : ownMaskPasses input)
    (hthin : (coordinate Label.thin
      (sliceAt input.time input.row.2)).val ≤ coordinatorThreshold input hvalid)
    (hfeedback : observationValue input =
      FiniteBanditModel.playerFeedback
        (fun i => pilotDraw (K_pos p) i (sliceAt input.time input.row.2))
        rewardRow.val (coordinator p.two_le_m)) :
    ∃ out, run input = some out ∧
      out.gateArm = some input.ownArm ∧
      collectionCoordinatorSourceMapPart input hvalid true = some input.ownArm ∧
      out.rawArrival =
        collectionCoordinatorSourceIncrement input hvalid true rewardRow := by
  have howns : ownsArm input.mode input.ownArm := by
    simp [ownsArm, hmode]
  have hrecord : SnapshotRecordingKernel.recordingMap p .collection true
      input.eta hvalid.eta_pos hvalid.eta_source_cap input.anchor
      input.currentWeights hvalid.anchor_pos hvalid.current_pos
      hvalid.anchor_le_current hvalid.current_le_twice_anchor
      (sliceAt input.time input.row.2) = some input.ownArm := by
    apply (SnapshotRecordingKernel.recordingMap_some_iff p .collection
      input.eta hvalid.eta_pos hvalid.eta_source_cap input.anchor
      input.currentWeights hvalid.anchor_pos hvalid.current_pos
      hvalid.anchor_le_current hvalid.current_le_twice_anchor
      (sliceAt input.time input.row.2) input.ownArm).2
    have hthreshold := collectionThreshold_eq_snapshot input hvalid hmode
    have hsource' : recorderSourceFromScalar p.two_le_m
        (coordinate Label.rec (sliceAt input.time input.row.2)) =
          coordinator p.two_le_m := by
      simpa [selectedRecorder] using hsource
    have hmask' : recordingMask (K_pos p)
        (recorderSourceFromScalar p.two_le_m
          (coordinate Label.rec (sliceAt input.time input.row.2)))
        input.ownArm (sliceAt input.time input.row.2) := by
      simpa [ownMaskPasses, hsource'] using hmask
    have hthin' : (coordinate Label.thin
        (sliceAt input.time input.row.2)).val ≤
          SnapshotRecordingKernel.thinningThreshold p .collection input.eta
            hvalid.eta_pos hvalid.eta_source_cap input.anchor input.currentWeights
            hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
            hvalid.current_le_twice_anchor
            (recorderSourceFromScalar p.two_le_m
              (coordinate Label.rec (sliceAt input.time input.row.2)))
            input.ownArm := by
      simpa [hsource', hthreshold] using hthin
    refine ⟨hdata, ?_, ?_, hmask', hthin'⟩
    · simpa [SnapshotRecordingKernel.dataAction, hsource'] using harm.symm
    · simp [SnapshotRecordingKernel.owns, hsource']
  have hphysical :=
    SnapshotRecordingKernel.collectionPhysicalIncrement_eq_floor p
      input.eta hvalid.eta_pos hvalid.eta_source_cap input.anchor
      input.currentWeights hvalid.anchor_pos hvalid.current_pos
      hvalid.anchor_le_current hvalid.current_le_twice_anchor
      (sliceAt input.time input.row.2) rewardRow input.ownArm hrecord
  have hownerFeedback :=
    SnapshotRecordingKernel.collection_recording_feedback p
      input.eta hvalid.eta_pos hvalid.eta_source_cap input.anchor
      input.currentWeights hvalid.anchor_pos hvalid.current_pos
      hvalid.anchor_le_current hvalid.current_le_twice_anchor
      (sliceAt input.time input.row.2) rewardRow input.ownArm hrecord
  have hsource' : recorderSourceFromScalar p.two_le_m
      (coordinate Label.rec (sliceAt input.time input.row.2)) =
        coordinator p.two_le_m := by
    simpa [selectedRecorder] using hsource
  rw [hsource'] at hownerFeedback
  have hobs : observationValue input = rewardRow.val input.ownArm := by
    calc
      observationValue input =
          FiniteBanditModel.playerFeedback
            (fun i => pilotDraw (K_pos p) i (sliceAt input.time input.row.2))
            rewardRow.val (coordinator p.two_le_m) := hfeedback
      _ = rewardRow.val input.ownArm := hownerFeedback
  have hobs' : realRewardGridValue (D p) (D_pos p) input.observation =
      rewardRow.val input.ownArm := by
    simpa [observationValue] using hobs
  have hfloor : floorArrival input = Nat.floor
      ((D p : ℝ) * input.eta * rewardRow.val input.ownArm /
        xi p input.eta input.anchor input.ownArm) := by
    unfold floorArrival
    rw [hobs']
  have hlocal := executeValid_gate_and_floor input hvalid hdata hsource
    hnotfrozen howns hmask hthin
  rcases hlocal with ⟨out, hout, hgate, harrival⟩
  have hrun : run input = some out := by
    simp [run, hvalid, hout]
  have hpart : collectionCoordinatorSourceMapPart input hvalid true =
      some input.ownArm := by
    simp [collectionCoordinatorSourceMapPart, hsource, hrecord]
  have hinc : collectionCoordinatorSourceIncrement input hvalid true rewardRow =
      Nat.floor ((D p : ℝ) * input.eta * rewardRow.val input.ownArm /
        xi p input.eta input.anchor input.ownArm) := by
    simpa [collectionCoordinatorSourceIncrement, hsource] using hphysical
  exact ⟨out, hrun, hgate, hpart, harrival.trans (hfloor.trans hinc.symm)⟩

/-- A conditional one-slice live comparison. The local operation and snapshot
kernel use the identical public-row slice at `sourceCalendarRound input`. The
coordinator's action and feedback are supplied by the accepted live
action/feedback functions. Under those local inputs, the successful gate and
arrival equal the coordinator-source part of the snapshot map and
`livePhysicalIncrement`. -/
theorem live_coordinator_recording_agrees {p : Parameters}
    (input : Input p) (hvalid : InputsValid input)
    (assignment : Assignment p.m p.K) (confirmationsEmpty : Bool)
    (snapshot : Snapshot assignment) {B : ℕ}
    (down up : HashedWord B) (rewardRow : RewardRow p.K)
    (hmode : input.mode = .live assignment confirmationsEmpty)
    (hmissing : snapshot.missing = ∅ ↔ confirmationsEmpty = true)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotfrozen : ¬ isFrozen input)
    (howns : ownsArm input.mode input.ownArm)
    (harm : input.ownArm = ActiveRoundActions.actions p.two_le_m snapshot
      (SnapshotRecordingKernel.liveRoundInput p input.eta hvalid.eta_pos
        hvalid.eta_source_cap input.anchor input.currentWeights
        hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
        hvalid.current_le_twice_anchor assignment down up
        (sliceAt input.time input.row.2)) (coordinator p.two_le_m))
    (hmask : ownMaskPasses input)
    (hthin : (coordinate Label.thin
      (sliceAt input.time input.row.2)).val ≤ coordinatorThreshold input hvalid)
    (hfeedback : observationValue input =
      ActiveRoundActions.feedback p.two_le_m snapshot
        (SnapshotRecordingKernel.liveRoundInput p input.eta hvalid.eta_pos
          hvalid.eta_source_cap input.anchor input.currentWeights
          hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
          hvalid.current_le_twice_anchor assignment down up
          (sliceAt input.time input.row.2)) rewardRow (coordinator p.two_le_m)) :
    ∃ out, run input = some out ∧
      out.gateArm = some input.ownArm ∧
      liveCoordinatorSourceMapPart input hvalid assignment snapshot true =
        some input.ownArm ∧
      out.rawArrival =
        liveCoordinatorSourceIncrement input hvalid assignment snapshot down up
          true rewardRow := by
  have howns' : input.ownArm ∉ (assignmentSlowSet p assignment).val := by
    simpa [ownsArm, hmode] using howns
  have hsource' : recorderSourceFromScalar p.two_le_m
      (coordinate Label.rec (sliceAt input.time input.row.2)) =
        coordinator p.two_le_m := by
    simpa [selectedRecorder] using hsource
  have hthreshold := liveThreshold_eq_snapshot input hvalid assignment
    confirmationsEmpty snapshot hmode hmissing
  have hthreshold' : coordinatorThreshold input hvalid =
      SnapshotRecordingKernel.thinningThreshold p (.live assignment snapshot)
        input.eta hvalid.eta_pos hvalid.eta_source_cap input.anchor
        input.currentWeights hvalid.anchor_pos hvalid.current_pos
        hvalid.anchor_le_current hvalid.current_le_twice_anchor
        (recorderSourceFromScalar p.two_le_m
          (coordinate Label.rec (sliceAt input.time input.row.2))) input.ownArm := by
    simpa [hsource'] using hthreshold
  have hmask' : recordingMask (K_pos p)
      (recorderSourceFromScalar p.two_le_m
        (coordinate Label.rec (sliceAt input.time input.row.2)))
      input.ownArm (sliceAt input.time input.row.2) := by
    simpa [ownMaskPasses, hsource'] using hmask
  have hthin' : (coordinate Label.thin
      (sliceAt input.time input.row.2)).val ≤
        SnapshotRecordingKernel.thinningThreshold p (.live assignment snapshot)
          input.eta hvalid.eta_pos hvalid.eta_source_cap input.anchor
          input.currentWeights hvalid.anchor_pos hvalid.current_pos
          hvalid.anchor_le_current hvalid.current_le_twice_anchor
          (recorderSourceFromScalar p.two_le_m
            (coordinate Label.rec (sliceAt input.time input.row.2))) input.ownArm := by
    simpa [hthreshold'] using hthin
  have haction : SnapshotRecordingKernel.dataAction p
      (.live assignment snapshot) input.eta hvalid.eta_pos
      hvalid.eta_source_cap input.anchor input.currentWeights
      hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
      hvalid.current_le_twice_anchor (sliceAt input.time input.row.2)
      (recorderSourceFromScalar p.two_le_m
        (coordinate Label.rec (sliceAt input.time input.row.2))) = input.ownArm := by
    rw [hsource']
    calc
      SnapshotRecordingKernel.dataAction p (.live assignment snapshot)
          input.eta hvalid.eta_pos hvalid.eta_source_cap input.anchor
          input.currentWeights hvalid.anchor_pos hvalid.current_pos
          hvalid.anchor_le_current hvalid.current_le_twice_anchor
          (sliceAt input.time input.row.2) (coordinator p.two_le_m) =
        ActiveRoundActions.actions p.two_le_m snapshot
          (SnapshotRecordingKernel.liveRoundInput p input.eta hvalid.eta_pos
            hvalid.eta_source_cap input.anchor input.currentWeights
            hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
            hvalid.current_le_twice_anchor assignment down up
            (sliceAt input.time input.row.2)) (coordinator p.two_le_m) :=
        SnapshotRecordingKernel.live_dataAction_eq_actions p input.eta
          hvalid.eta_pos hvalid.eta_source_cap input.anchor input.currentWeights
          hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
          hvalid.current_le_twice_anchor assignment snapshot down up
          (sliceAt input.time input.row.2) hdata (coordinator p.two_le_m)
      _ = input.ownArm := harm.symm
  have hownsKernel : SnapshotRecordingKernel.owns p (.live assignment snapshot)
      (recorderSourceFromScalar p.two_le_m
        (coordinate Label.rec (sliceAt input.time input.row.2))) input.ownArm := by
    rw [hsource']
    change input.ownArm ∉ Finset.univ.image assignment.assigned
    simpa [assignmentSlowSet] using howns'
  have hrecord : SnapshotRecordingKernel.recordingMap p
      (.live assignment snapshot) true input.eta hvalid.eta_pos
      hvalid.eta_source_cap input.anchor input.currentWeights
      hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
      hvalid.current_le_twice_anchor (sliceAt input.time input.row.2) =
        some input.ownArm := by
    apply (SnapshotRecordingKernel.recordingMap_some_iff p
      (.live assignment snapshot) input.eta hvalid.eta_pos
      hvalid.eta_source_cap input.anchor input.currentWeights
      hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
      hvalid.current_le_twice_anchor (sliceAt input.time input.row.2)
      input.ownArm).2
    exact ⟨hdata, haction, hownsKernel, hmask', hthin'⟩
  have hownerFeedback :=
    SnapshotRecordingKernel.live_recording_feedback p input.eta
      hvalid.eta_pos hvalid.eta_source_cap input.anchor input.currentWeights
      hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
      hvalid.current_le_twice_anchor assignment snapshot down up
      (sliceAt input.time input.row.2) rewardRow input.ownArm hrecord
  rw [hsource'] at hownerFeedback
  have hobs : observationValue input = rewardRow.val input.ownArm := by
    calc
      observationValue input =
          ActiveRoundActions.feedback p.two_le_m snapshot
            (SnapshotRecordingKernel.liveRoundInput p input.eta hvalid.eta_pos
              hvalid.eta_source_cap input.anchor input.currentWeights
              hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
              hvalid.current_le_twice_anchor assignment down up
              (sliceAt input.time input.row.2)) rewardRow (coordinator p.two_le_m) :=
        hfeedback
      _ = rewardRow.val input.ownArm := hownerFeedback
  have hobs' : realRewardGridValue (D p) (D_pos p) input.observation =
      rewardRow.val input.ownArm := by
    simpa [observationValue] using hobs
  have hfloor : floorArrival input = Nat.floor
      ((D p : ℝ) * input.eta * rewardRow.val input.ownArm /
        xi p input.eta input.anchor input.ownArm) := by
    unfold floorArrival
    rw [hobs']
  have hphysical :=
    SnapshotRecordingKernel.livePhysicalIncrement_eq_floor p input.eta
      hvalid.eta_pos hvalid.eta_source_cap input.anchor input.currentWeights
      hvalid.anchor_pos hvalid.current_pos hvalid.anchor_le_current
      hvalid.current_le_twice_anchor assignment snapshot down up
      (sliceAt input.time input.row.2) rewardRow input.ownArm hrecord
  have hlocal := executeValid_gate_and_floor input hvalid hdata hsource
    hnotfrozen howns hmask hthin
  rcases hlocal with ⟨out, hout, hgate, harrival⟩
  have hrun : run input = some out := by simp [run, hvalid, hout]
  have hpart : liveCoordinatorSourceMapPart input hvalid assignment snapshot
      true = some input.ownArm := by
    simp [liveCoordinatorSourceMapPart, hsource, hrecord]
  have hinc : liveCoordinatorSourceIncrement input hvalid assignment snapshot
      down up true rewardRow =
        Nat.floor ((D p : ℝ) * input.eta * rewardRow.val input.ownArm /
          xi p input.eta input.anchor input.ownArm) := by
    simpa [liveCoordinatorSourceIncrement, hsource] using hphysical
  exact ⟨out, hrun, hgate, hpart, harrival.trans (hfloor.trans hinc.symm)⟩

/-- If a DATA row selects another recorder, the coordinator-local result is
zero and its projected analysis part is `none`; the full map is intentionally
left to that selected player's local operation. -/
theorem otherRecorder_source_part_is_separate {p : Parameters}
    (input : Input p) (hvalid : InputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hother : selectedRecorder input ≠ coordinator p.two_le_m) :
    executeValid input hvalid = some (zeroOutput p) ∧
      collectionCoordinatorSourceMapPart input hvalid true = none := by
  exact ⟨executeValid_zero_of_other_source input hvalid hdata hother,
    by simp [collectionCoordinatorSourceMapPart, hother]⟩

/-- The same explicit source separation for a live snapshot: a selected
follower owns the row's recording event, so it contributes nothing to the
coordinator-local output or coordinator-source map projection. -/
theorem otherRecorder_live_source_part_is_separate {p : Parameters}
    (input : Input p) (hvalid : InputsValid input)
    (assignment : Assignment p.m p.K) (snapshot : Snapshot assignment)
    (enabled : Bool)
    (hdata : selectedSlot input = dataSlot)
    (hother : selectedRecorder input ≠ coordinator p.two_le_m) :
    executeValid input hvalid = some (zeroOutput p) ∧
      liveCoordinatorSourceMapPart input hvalid assignment snapshot enabled = none := by
  exact ⟨executeValid_zero_of_other_source input hvalid hdata hother,
    by simp [liveCoordinatorSourceMapPart, hother]⟩


end Bandits.Support.CoordinatorRecordingOperation

end
