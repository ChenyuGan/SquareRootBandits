/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedStayConditionalMean
public import Bandits.Support.GeneratedBootstrapFiltration
public import Bandits.Support.ReferenceInitializationRun
public import Bandits.Support.BootstrapPhysicalBlock

/-!
# Eventwise actual generated stay-gain tower bound

This module applies the accepted one-round DATA stay-positive lower bound to
the original generated run, conditional on its literal block-start event. The
gain observable is the existing physical all-slot stay gain, stopped only
when the generated reference run does not process the requested block or the
focal follower is not incoming.

Sources: sources/zip4/manuscript/appendix_b_communication.tex:376-395,485-506
and sources/zip4/manuscript/07_public_setup.tex:27-38,87-109.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.GeneratedStayBlockTower

abbrev Parameters := ConstructorDimensions.Parameters

open MeasureTheory
open ConstructorDimensions BootstrapDimensions CompletePublicTable
open ActiveRoundActions ReferencePrelaunchFollower
open GeneratedBootstrapRoundLaw GeneratedBootstrapFiltration
open ReferenceInitializationRun ReferenceInitializationMeasurability
open GeneratedStayConditionalMean BootstrapPhysicalBlock BootstrapPhysicalInput
open BootstrapModeService BootstrapWeightPotential
open scoped Classical BigOperators

variable {p : Parameters}

/-- The zero-based first physical round of a calendar bootstrap block. -/
def blockStartRound (p : Parameters) (s : Fin (n_boot p)) : Fin p.T :=
  ⟨s.val * B_boot p, by
    obtain ⟨t, ht⟩ := calendarBlock_nonempty p s
    have hmem := (mem_calendarBlock_iff p s t).mp ht
    omega⟩

theorem blockStartRound_mem (p : Parameters) (s : Fin (n_boot p)) :
    blockStartRound p s ∈ calendarBlock p s := by
  rw [mem_calendarBlock_iff]
  refine ⟨Nat.le_refl _, ?_⟩
  obtain ⟨t, ht⟩ := calendarBlock_nonempty p s
  have hmem := (mem_calendarBlock_iff p s t).mp ht
  simp only [blockStartRound]
  omega

/-- Literal start-boundary condition for the focal follower and its original
private ID, evaluated only on the actual generated descriptor. -/
def blockStartGuard (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    {s : Fin (n_boot p)} (i : Follower p.m) (a z : Fin p.K)
    (u : Fin (A_id p)) : Option (Descriptor p) → Prop
  | none => False
  | some d =>
    let x := GeneratedStayConditionalMean.inputOfDescriptor p ids rewards (s := s) d
    ∃ hi : i ∈ x.uninformed,
      let j : {j // j ∈ x.uninformed} := ⟨i, hi⟩
      x.active j = true ∧ x.held j = a ∧ x.privateId j = u ∧
        x.target = z ∧ z ≠ a ∧
        ∀ k : {j // j ∈ x.uninformed}, k ≠ j → x.active k = false

/-- The original-coordinate event that the requested block is processed,
the focal follower is incoming and active with held arm a and U=u, the actual
target is z ≠ a, and every other incoming follower is inactive. -/
def blockStartEvent (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) (a z : Fin p.K)
    (u : Fin (A_id p)) : Set (Coordinates p) :=
  {e | blockStartGuard ids rewards (s := s) i a z u
    (descriptor p ids rewards C_star C_h eta s (blockStartRound p s) e)}

/-- On the specified event the accepted one-round isolation guard holds. -/
theorem blockStartGuard_implies_isolation (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    {s : Fin (n_boot p)} (i : Follower p.m) (a z : Fin p.K)
    (u : Fin (A_id p)) (d : Descriptor p)
    (hg : blockStartGuard ids rewards (s := s) i a z u (some d)) :
    GeneratedStayConditionalMean.isolationGuard p ids rewards (s := s) i a z
      (some d) := by
  dsimp [blockStartGuard, GeneratedStayConditionalMean.isolationGuard,
    GeneratedStayConditionalMean.inputOfDescriptor] at hg ⊢
  rcases hg with ⟨hi, hactive, hheld, hprivate, htarget, hza, hinactive⟩
  exact ⟨hi, hactive, hheld, htarget, hza, hinactive⟩

/-- Literal fixed reward support chi_t(a). -/
def sourceChi (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (t : Fin p.T) (a : Fin p.K) : ℝ :=
  if 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a)
  then 1 else 0

/-- The fixed-original-ID coefficient appearing in the eventwise gain bound. -/
def blockStartGainCoefficient (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    {s : Fin (n_boot p)} (a : Fin p.K) (u : Fin (A_id p)) : ℝ :=
  ∑ t ∈ calendarBlock p s,
    sourceChi rewards t a * (if ids u t = false then 1 else 0) / 16

theorem sourceChi_nonneg (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (t : Fin p.T) (a : Fin p.K) : 0 ≤ sourceChi rewards t a := by
  unfold sourceChi
  split_ifs <;> norm_num

theorem blockStartGainCoefficient_nonneg (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    {s : Fin (n_boot p)} (a : Fin p.K) (u : Fin (A_id p)) :
    0 ≤ blockStartGainCoefficient ids rewards (s := s) a u := by
  apply Finset.sum_nonneg
  intro t ht
  have hchi := sourceChi_nonneg rewards t a
  have hid : 0 ≤ (if ids u t = false then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  exact div_nonneg (mul_nonneg hchi hid) (by norm_num)

private theorem blockStartGuard_dataStayLowerBound (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    {s : Fin (n_boot p)} (t : Fin p.T) (i : Follower p.m)
    (a z : Fin p.K) (u : Fin (A_id p)) (d : Descriptor p)
    (hg : blockStartGuard ids rewards (s := s) i a z u (some d)) :
    GeneratedStayConditionalMean.dataStayLowerBound p ids rewards (s := s) t i a
      (some d) = sourceChi rewards t a * (if ids u t = false then 1 else 0) / 16 := by
  dsimp [blockStartGuard] at hg
  rcases hg with ⟨hi, hactive, hheld, hprivate, htarget, hza, hinactive⟩
  let x := GeneratedStayConditionalMean.inputOfDescriptor p ids rewards (s := s) d
  let j : {j // j ∈ x.uninformed} := ⟨i, hi⟩
  have hu : x.privateId j = u := hprivate
  change (if h : i ∈ x.uninformed then
      BootstrapModeService.chi x t a *
        (if ids (x.privateId ⟨i, h⟩) t = false then 1 else 0) / 16
    else 0) = _
  rw [dif_pos hi, hu]
  simp [sourceChi, BootstrapModeService.chi, x,
    GeneratedStayConditionalMean.inputOfDescriptor]

/-- The accepted actual DATA stay tests summed over the calendar block,
including the shortened final block. -/
def blockDataStaySum (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) : Coordinates p → ℝ := fun e =>
  ∑ t ∈ calendarBlock p s,
    GeneratedStayConditionalMean.actualDataStayTest p ids rewards C_star C_h eta
      (s := s) t i e

/-- Existing physical all-slot gain at a generated boundary. The two zero
branches are exactly the stopped run and nonincoming focal follower cases. -/
def gainAtBoundary (x : ReferenceInitializationRun.Input p)
    (b : Boundary p) (i : Follower p.m) : ℝ :=
  if hc : b.crossing = none then
    if h : b.completed < n_boot p then
      let y := ReferenceInitializationRun.physical x b h
      if hi : i ∈ y.uninformed then
        (BootstrapPhysicalBlock.physicalStayGain y ⟨i, hi⟩ : ℝ)
      else 0
    else 0
  else 0

/-- The honest stopped total gain observable from the actual generated run. -/
def actualBlockGain (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) : Coordinates p → ℝ := fun e =>
  let x := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  gainAtBoundary x (ReferenceInitializationRun.run x s.val) i

theorem blockStartEvent_measurable (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) (a z : Fin p.K)
    (u : Fin (A_id p)) :
    MeasurableSet[analysisFiltration p (blockStartRound p s).val]
      (blockStartEvent ids rewards C_star C_h eta (s := s) i a z u) := by
  have hd := GeneratedBootstrapFiltration.measurable_descriptor p ids rewards C_star C_h eta
    s (blockStartRound p s) (blockStartRound_mem p s)
  have hs : MeasurableSet {d : Option (Descriptor p) |
      blockStartGuard ids rewards (s := s) i a z u d} :=
    MeasurableSpace.measurableSet_top
  change MeasurableSet[analysisFiltration p (blockStartRound p s).val]
    ((descriptor p ids rewards C_star C_h eta s (blockStartRound p s)) ⁻¹'
      {d : Option (Descriptor p) |
        blockStartGuard ids rewards (s := s) i a z u d})
  exact hs.preimage hd

private theorem physicalStayGain_nonneg_le_B {s : Fin (n_boot p)}
    (x : BootstrapPhysicalBlock.Input p s) (j : {j // j ∈ x.uninformed}) :
    0 ≤ (BootstrapPhysicalBlock.physicalStayGain x j : ℝ) ∧
      (BootstrapPhysicalBlock.physicalStayGain x j : ℝ) ≤ B_boot p := by
  have hsub : BootstrapPhysicalBlock.physicalStayRounds x j ⊆ calendarBlock p s := by
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  have hcard : (BootstrapPhysicalBlock.physicalStayRounds x j).card ≤ B_boot p :=
    (Finset.card_le_card hsub).trans (calendarBlock_card_le_B_boot p s)
  unfold BootstrapPhysicalBlock.physicalStayGain
  split_ifs with ha
  · exact ⟨Nat.cast_nonneg _, Nat.cast_le.mpr hcard⟩
  · simp

theorem gainAtBoundary_nonneg_le_B (x : ReferenceInitializationRun.Input p)
    (b : Boundary p) (i : Follower p.m) :
    0 ≤ gainAtBoundary x b i ∧ gainAtBoundary x b i ≤ B_boot p := by
  by_cases hc : b.crossing = none
  · by_cases h : b.completed < n_boot p
    · let y := ReferenceInitializationRun.physical x b h
      by_cases hi : i ∈ y.uninformed
      · simpa [gainAtBoundary, hc, h, hi, y] using
          physicalStayGain_nonneg_le_B y ⟨i, hi⟩
      · constructor <;> simp [gainAtBoundary, hc, h, hi, y] <;> positivity
    · constructor <;> simp [gainAtBoundary, hc, h] <;> positivity
  · constructor <;> simp [gainAtBoundary, hc] <;> positivity

theorem actualBlockGain_nonneg_le_B (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) (e : Coordinates p) :
    0 ≤ actualBlockGain ids rewards C_star C_h eta (s := s) i e ∧
      actualBlockGain ids rewards C_star C_h eta (s := s) i e ≤ B_boot p := by
  let x := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  exact gainAtBoundary_nonneg_le_B x (ReferenceInitializationRun.run x s.val) i
private theorem measurable_gainAtBoundary_coordinates
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (b : Boundary p) (i : Follower p.m) :
    Measurable (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
      gainAtBoundary
        (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards z)
        b i) := by
  by_cases hc : b.crossing = none
  · by_cases h : b.completed < n_boot p
    · let incoming := ReferenceInitializationRun.uninformed b
      by_cases hi : i ∈ incoming
      · let j : {j // j ∈ incoming} := ⟨i, hi⟩
        let X := ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
        let draws := ReferenceInitializationMeasurability.blockDrawCode p
          (ReferenceInitializationRun.nextBlock b h) incoming b.numerators b.weight_ge_one
        have hdraw := ReferenceInitializationMeasurability.measurable_blockDrawCode p
          (ReferenceInitializationRun.nextBlock b h) incoming b.numerators b.weight_ge_one
        have hactiveCode : Measurable
            (fun z : ReferenceInitializationMeasurability.InputCoordinates p => (draws z).1 j) :=
          (measurable_pi_apply j).comp (measurable_fst.comp hdraw)
        have hgain := ReferenceInitializationMeasurability.measurable_weightGain_at_fixedBoundary
          p C_star C_h eta rewards b h j
        have hactive : Measurable
            (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
              (ReferenceInitializationRun.weightInput (X z) b h j).enabled) := by
          have heq : (fun z =>
              (ReferenceInitializationRun.weightInput (X z) b h j).enabled) =
              fun z => (draws z).1 j := by
            funext z
            rw [(ReferenceInitializationMeasurability.weightInput_fields (X z) b h j).1]
            rfl
          rw [heq]
          exact hactiveCode
        have hpair : Measurable
            (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
              ((ReferenceInitializationRun.weightInput (X z) b h j).enabled,
                (ReferenceInitializationRun.weightInput (X z) b h j).gain)) :=
          hactive.prodMk hgain
        have heff : Measurable
            (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
              BootstrapWeightPotential.effectiveGain
                (ReferenceInitializationRun.weightInput (X z) b h j)) := by
          change Measurable (fun z => if
            (ReferenceInitializationRun.weightInput (X z) b h j).enabled then
              (ReferenceInitializationRun.weightInput (X z) b h j).gain else 0)
          exact (measurable_of_countable (fun q : Bool × ℕ => if q.1 then q.2 else 0)).comp hpair
        have hphys : (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
            BootstrapPhysicalBlock.physicalStayGain
              (ReferenceInitializationRun.physical (X z) b h) j) =
          fun z => BootstrapWeightPotential.effectiveGain
              (ReferenceInitializationRun.weightInput (X z) b h j) := by
          funext z
          exact (ReferenceInitializationRun.weightInput_full_gain (X z) b h j).symm
        have hcast : Measurable
            (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
              (BootstrapWeightPotential.effectiveGain
                (ReferenceInitializationRun.weightInput (X z) b h j) : ℝ)) :=
          (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp heff
        have hreal : Measurable
            (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
              (BootstrapPhysicalBlock.physicalStayGain
                (ReferenceInitializationRun.physical (X z) b h) j : ℝ)) := by
          have hEqReal : (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
              (BootstrapPhysicalBlock.physicalStayGain
                (ReferenceInitializationRun.physical (X z) b h) j : ℝ)) =
              fun z => (BootstrapWeightPotential.effectiveGain
                (ReferenceInitializationRun.weightInput (X z) b h j) : ℝ) := by
            funext z
            exact congrArg (fun n : ℕ => (n : ℝ)) (congrFun hphys z)
          rw [hEqReal]
          exact hcast
        have hfinal : (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
            gainAtBoundary (X z) b i) =
          fun z => (BootstrapPhysicalBlock.physicalStayGain
            (ReferenceInitializationRun.physical (X z) b h) j : ℝ) := by
          funext z
          let y := ReferenceInitializationRun.physical (X z) b h
          have hy : y.uninformed = incoming := rfl
          simp [gainAtBoundary, hc, h, hi, j, X, incoming, y, hy]
          congr 2
        rw [hfinal]
        exact hreal
      · have hzero : (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
            gainAtBoundary
              (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards z)
              b i) = fun _ => 0 := by
          funext z
          have hiy : i ∉
              (ReferenceInitializationRun.physical
                (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards z)
                b h).uninformed := by
            change i ∉ incoming
            exact hi
          simp [gainAtBoundary, hc, h, hiy]
        rw [hzero]
        exact measurable_const
    · have hzero : (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
          gainAtBoundary
            (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards z)
            b i) = fun _ => 0 := by
        funext z
        simp [gainAtBoundary, hc, h]
      rw [hzero]
      exact measurable_const
  · have hzero : (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
        gainAtBoundary
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards z)
          b i) = fun _ => 0 := by
      funext z
      simp [gainAtBoundary, hc]
    rw [hzero]
    exact measurable_const

theorem measurable_actualBlockGain (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) :
    Measurable (actualBlockGain ids rewards C_star C_h eta (s := s) i) := by
  let X := ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
  have hcoord : Measurable (fun e : Coordinates p => (ids, e)) :=
    measurable_const.prodMk measurable_id
  have hrun : Measurable (fun e : Coordinates p =>
      ReferenceInitializationRun.run (X (ids, e)) s.val) :=
    (ReferenceInitializationMeasurability.measurable_run p C_star C_h eta rewards s.val).comp hcoord
  have hpair : Measurable (fun e : Coordinates p =>
      (ReferenceInitializationRun.run (X (ids, e)) s.val, (ids, e))) := hrun.prodMk hcoord
  have hbranches : Measurable (fun q : Boundary p ×
      ReferenceInitializationMeasurability.InputCoordinates p =>
      gainAtBoundary (X q.2) q.1 i) := by
    apply measurable_from_prod_countable_right
    intro b
    exact measurable_gainAtBoundary_coordinates ids rewards C_star C_h eta b i
  change Measurable (fun e : Coordinates p =>
    gainAtBoundary (X (ids, e))
      (ReferenceInitializationRun.run (X (ids, e)) s.val) i)
  exact hbranches.comp hpair

theorem integrable_actualBlockGain (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) :
    Integrable (actualBlockGain ids rewards C_star C_h eta (s := s) i)
      (originalLaw p) := by
  have hmeas := measurable_actualBlockGain ids rewards C_star C_h eta (s := s) i
  refine (integrable_const (B_boot p : ℝ)).mono'
    hmeas.stronglyMeasurable.aestronglyMeasurable ?_
  filter_upwards with e
  have h := actualBlockGain_nonneg_le_B ids rewards C_star C_h eta (s := s) i e
  have hB : (0 : ℝ) ≤ (B_boot p : ℝ) := Nat.cast_nonneg _
  simpa [Real.norm_eq_abs, abs_of_nonneg hB] using
    (abs_le.mpr ⟨by linarith [h.1], h.2⟩)
/-- At each member round of a processed opportunity, the descriptor is
reconstructed from the same generated boundary, actual block draw profile,
and actual target. Only its pre-choice state advances with the round. -/
private theorem descriptor_eq_actualPhysical (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (t : Fin p.T) (e : Coordinates p)
    (hc : (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing = none) :
    ∃ h : (ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).completed <
          n_boot p,
      descriptor p ids rewards C_star C_h eta s t e =
        some
          (ReferenceInitializationRun.run
              (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val,
            (BootstrapPhysicalInput.currentBlockDrawProfile p
                (ReferenceInitializationRun.nextBlock
                  (ReferenceInitializationRun.run
                    (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val) h)
                (ReferenceInitializationRun.run
                  (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).numerators
                (ReferenceInitializationRun.run
                  (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).weight_ge_one
                (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e).coordinates,
              ((ReferenceInitializationRun.physical
                  (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
                  (ReferenceInitializationRun.run
                    (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val) h).target,
                BootstrapPhysicalBlock.run
                  (ReferenceInitializationRun.physical
                    (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
                    (ReferenceInitializationRun.run
                      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val) h)
                  t.val))) := by
  let x := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let b := ReferenceInitializationRun.run x s.val
  have hc' : b.crossing = none := by simpa [b, x] using hc
  have hno : b.crossing.isSome ≠ true := by
    rw [hc']
    simp
  have hcompleted : b.completed = s.val :=
    (ReferenceInitializationRun.run_progress x s.val s.isLt.le).resolve_left hno
  have hrem : b.completed < n_boot p := by
    rw [hcompleted]
    exact s.isLt
  refine ⟨hrem, ?_⟩
  change GeneratedBootstrapRoundLaw.descriptorAtBoundary p x b t = _
  simp [GeneratedBootstrapRoundLaw.descriptorAtBoundary, hc, hrem, x, b]

/-- The actual start-event guard persists throughout the same processed
physical block. The boundary, incoming set, draw profile, and target are
reconstructed from the generated run at each round; no descriptor identity is
assumed. -/
theorem blockStartGuard_persists (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) (a z : Fin p.K)
    (u : Fin (A_id p)) (e : Coordinates p)
    (hE : e ∈ blockStartEvent ids rewards C_star C_h eta (s := s) i a z u)
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) :
    ∃ d : Descriptor p,
      descriptor p ids rewards C_star C_h eta s t e = some d ∧
      blockStartGuard ids rewards (s := s) i a z u (some d) := by
  let t₀ := blockStartRound p s
  change blockStartGuard ids rewards (s := s) i a z u
    (descriptor p ids rewards C_star C_h eta s t₀ e) at hE
  cases hd₀ : descriptor p ids rewards C_star C_h eta s t₀ e with
  | none =>
      simp [blockStartGuard, hd₀] at hE
  | some d₀ =>
      have hg₀ : blockStartGuard ids rewards (s := s) i a z u (some d₀) := by
        simpa [hd₀] using hE
      rcases d₀ with ⟨b₀, draws₀, z₀, st₀⟩
      have hrec := GeneratedStayConditionalMean.actualDescriptor_reconstructs_source_block
        p ids rewards C_star C_h eta (s := s) t₀ e
        (b₀, (draws₀, (z₀, st₀))) hd₀
      dsimp only at hrec
      rcases hrec with ⟨hb, hrest⟩
      rcases hrest with ⟨hrem₀, hprofile₀, htarget₀, hstate₀, hnext₀⟩
      subst b₀
      let x := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
      let b := ReferenceInitializationRun.run x s.val
      have hdescNotNone :
          descriptor p ids rewards C_star C_h eta s t₀ e ≠ none := by
        rw [hd₀]
        simp
      have hc : b.crossing = none := by
        by_contra hcross
        have hnone :=
          (GeneratedBootstrapRoundLaw.descriptor_eq_none_iff ids rewards C_star C_h eta s t₀ e).2
            hcross
        exact hdescNotNone hnone
      have hprof :
          BootstrapPhysicalInput.currentBlockDrawProfile p
            (ReferenceInitializationRun.nextBlock b hrem₀) b.numerators b.weight_ge_one
            x.coordinates = draws₀ := by
        simpa [b, x] using hprofile₀
      have htarget :
          (ReferenceInitializationRun.physical x b hrem₀).target = z₀ := by
        simpa [b, x] using htarget₀
      have hdescₜ := descriptor_eq_actualPhysical ids rewards C_star C_h eta
        (s := s) t e hc
      rcases hdescₜ with ⟨hremₜ, hactualₜ⟩
      let stₜ := BootstrapPhysicalBlock.run
        (ReferenceInitializationRun.physical x b hremₜ) t.val
      have hdesc : descriptor p ids rewards C_star C_h eta s t e =
          some (b, (draws₀, (z₀, stₜ))) := by
        simpa [b, x, stₜ, hprof, htarget] using hactualₜ
      refine ⟨(b, (draws₀, (z₀, stₜ))), hdesc, ?_⟩
      dsimp only [blockStartGuard] at hg₀ ⊢
      simpa [GeneratedStayConditionalMean.inputOfDescriptor] using hg₀

/-- On a processed boundary and incoming focal follower, the stopped gain is
exactly the existing reference weight updater's full effective gain. That
updater uses all physical stay slots, including observations after saving. -/
theorem actualBlockGain_eq_referenceEffectiveGain (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) (e : Coordinates p)
    (hc : (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing = none)
    (hrem : (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).completed < n_boot p)
    (hi : i ∈ ReferenceInitializationRun.uninformed
      (ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val)) :
    actualBlockGain ids rewards C_star C_h eta (s := s) i e =
      (BootstrapWeightPotential.effectiveGain
        (ReferenceInitializationRun.weightInput
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
          (ReferenceInitializationRun.run
            (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val)
          hrem ⟨i, hi⟩) : ℝ) := by
  let x := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let b := ReferenceInitializationRun.run x s.val
  have hfull := ReferenceInitializationRun.weightInput_full_gain x b hrem ⟨i, hi⟩
  have hiPhysical : i ∈ (ReferenceInitializationRun.physical x b hrem).uninformed := by
    change i ∈ ReferenceInitializationRun.uninformed b
    exact hi
  calc
    actualBlockGain ids rewards C_star C_h eta (s := s) i e =
        (BootstrapPhysicalBlock.physicalStayGain
          (ReferenceInitializationRun.physical x b hrem) ⟨i, hi⟩ : ℝ) := by
      simp [actualBlockGain, gainAtBoundary, hc, hrem, hiPhysical, x, b]
    _ = (BootstrapWeightPotential.effectiveGain
        (ReferenceInitializationRun.weightInput x b hrem ⟨i, hi⟩) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hfull.symm

private theorem physicalStayIndicator_sum_eq_gain {s : Fin (n_boot p)}
    (y : BootstrapPhysicalBlock.Input p s) (j : {j // j ∈ y.uninformed}) :
    (∑ t ∈ calendarBlock p s,
      if y.active j = true ∧ t ∈ BootstrapPhysicalBlock.physicalStayRounds y j
      then (1 : ℝ) else 0) = (BootstrapPhysicalBlock.physicalStayGain y j : ℝ) := by
  by_cases ha : y.active j = true
  · have hsubset : BootstrapPhysicalBlock.physicalStayRounds y j ⊆ calendarBlock p s := by
      intro t ht
      exact (Finset.mem_filter.mp ht).1
    have hfilter : (calendarBlock p s).filter
        (fun t => t ∈ BootstrapPhysicalBlock.physicalStayRounds y j) =
        BootstrapPhysicalBlock.physicalStayRounds y j := by
      ext t
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro ht
        exact ⟨hsubset ht, ht⟩
    calc
      (∑ t ∈ calendarBlock p s,
        if y.active j = true ∧ t ∈ BootstrapPhysicalBlock.physicalStayRounds y j
        then (1 : ℝ) else 0) =
          ∑ t ∈ calendarBlock p s,
            if t ∈ BootstrapPhysicalBlock.physicalStayRounds y j then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro t ht
              simp [ha]
      _ = ((calendarBlock p s).filter
          (fun t => t ∈ BootstrapPhysicalBlock.physicalStayRounds y j)).card := by
            simp only [Finset.sum_boole]
      _ = (BootstrapPhysicalBlock.physicalStayRounds y j).card := by rw [hfilter]
      _ = (BootstrapPhysicalBlock.physicalStayGain y j : ℝ) := by
            simp [BootstrapPhysicalBlock.physicalStayGain, ha]
  · simp [ha, BootstrapPhysicalBlock.physicalStayGain]

private theorem actualDataStayTest_le_physicalStayIndicator (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) (e : Coordinates p)
    (b : Boundary p)
    (hb : ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val = b)
    (hc : b.crossing = none) (hrem : b.completed < n_boot p)
    (hi : i ∈ ReferenceInitializationRun.uninformed b)
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) :
    GeneratedStayConditionalMean.actualDataStayTest p ids rewards C_star C_h eta
        (s := s) t i e ≤
      if (ReferenceInitializationRun.physical
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b hrem).active
            ⟨i, by change i ∈ ReferenceInitializationRun.uninformed b; exact hi⟩ = true ∧
          t ∈ BootstrapPhysicalBlock.physicalStayRounds
            (ReferenceInitializationRun.physical
              (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) b hrem)
            ⟨i, by change i ∈ ReferenceInitializationRun.uninformed b; exact hi⟩
      then 1 else 0 := by
  subst b
  let x := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  have hcRun : (ReferenceInitializationRun.run x s.val).crossing = none := by
    simpa [x] using hc
  rcases descriptor_eq_actualPhysical ids rewards C_star C_h eta (s := s) t e hcRun with
    ⟨hactual, hactualDesc⟩
  let b := ReferenceInitializationRun.run x s.val
  let y := ReferenceInitializationRun.physical x b hactual
  let draws := BootstrapPhysicalInput.currentBlockDrawProfile p
    (ReferenceInitializationRun.nextBlock b hactual) b.numerators b.weight_ge_one x.coordinates
  let st := BootstrapPhysicalBlock.run y t.val
  have hdesc : descriptor p ids rewards C_star C_h eta s t e =
      some (b, (draws, (y.target, st))) := by
    simpa [x, b, y, draws, st] using hactualDesc
  have hsource := GeneratedStayConditionalMean.actualDataStayTest_eq_sourceStayPositive
    p ids rewards C_star C_h eta (s := s) t i e b draws y.target st hdesc hi
  rcases hsource with ⟨hsource, htest, _, hchar, _, hnext⟩
  have hsourceEq : hsource = hactual := Subsingleton.elim _ _
  subst hsource
  have hremEq : hrem = hactual := Subsingleton.elim _ _
  subst hrem
  have hnextActual : ReferenceInitializationRun.nextBlock b hactual = s := by
    simpa using hnext
  let j : {j // j ∈ y.uninformed} :=
    ⟨i, by change i ∈ ReferenceInitializationRun.uninformed b; exact hi⟩
  have hchar' : BootstrapStayAvoidance.dataStayPositive y st t j
      (roundCoordinates p t y.row)
      (BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars y
        (fun q => BootstrapPhysicalInput.playerRoundScalarAt p x.coordinates q t)) =
    if y.active j = true ∧ y.ids (y.privateId j) t = false ∧
        BootstrapPhysicalBlock.slot y t = PublicDiscreteDraws.dataSlot ∧
        0 < BootstrapPhysicalBlock.feedback y st t
          (PublicDiscreteDraws.followerPlayer p.two_le_m j.1)
    then 1 else 0 := by
    simpa [x, y, j] using hchar
  rw [htest, hchar']
  by_cases hpositive : y.active j = true ∧ y.ids (y.privateId j) t = false ∧
      BootstrapPhysicalBlock.slot y t = PublicDiscreteDraws.dataSlot ∧
      0 < BootstrapPhysicalBlock.feedback y st t
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.1)
  · have hstay : t ∈ BootstrapPhysicalBlock.physicalStayRounds y j := by
      simp [BootstrapPhysicalBlock.physicalStayRounds, hnextActual, ht,
        hpositive.2.1, hpositive.2.2.2, st]
    have hindicator :
        (ReferenceInitializationRun.physical x b hactual).active
            ⟨i, by change i ∈ ReferenceInitializationRun.uninformed b; exact hi⟩ = true ∧
          t ∈ BootstrapPhysicalBlock.physicalStayRounds
            (ReferenceInitializationRun.physical x b hactual)
            ⟨i, by change i ∈ ReferenceInitializationRun.uninformed b; exact hi⟩ := by
      constructor
      · simpa [x, b, y, j] using hpositive.1
      · simpa [x, b, y, j] using hstay
    simp [x, b, hpositive, hindicator]
  · simp only [if_neg hpositive]
    split_ifs <;> norm_num

private theorem actualDataStayTest_eq_zero_of_notIncoming (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) (e : Coordinates p)
    (b : Boundary p)
    (hb : ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val = b)
    (hc : b.crossing = none) (hrem : b.completed < n_boot p)
    (hi : i ∉ ReferenceInitializationRun.uninformed b) (t : Fin p.T) :
    GeneratedStayConditionalMean.actualDataStayTest p ids rewards C_star C_h eta
      (s := s) t i e = 0 := by
  subst b
  let x := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  have hcRun : (ReferenceInitializationRun.run x s.val).crossing = none := by
    simpa [x] using hc
  rcases descriptor_eq_actualPhysical ids rewards C_star C_h eta (s := s) t e hcRun with
    ⟨hactual, hactualDesc⟩
  let b := ReferenceInitializationRun.run x s.val
  let y := ReferenceInitializationRun.physical x b hactual
  let draws := BootstrapPhysicalInput.currentBlockDrawProfile p
    (ReferenceInitializationRun.nextBlock b hactual) b.numerators b.weight_ge_one x.coordinates
  let st := BootstrapPhysicalBlock.run y t.val
  have hdesc : descriptor p ids rewards C_star C_h eta s t e =
      some (b, (draws, (y.target, st))) := by
    simpa [x, b, y, draws, st] using hactualDesc
  change GeneratedStayConditionalMean.dataStayTest p ids rewards (s := s) t i
    (descriptor p ids rewards C_star C_h eta s t e, current p t e) = 0
  simp [GeneratedBootstrapFiltration.testValue, hdesc,
    GeneratedStayConditionalMean.dataStayTest,
    GeneratedStayConditionalMean.inputOfDescriptor, x, b, hi]

/-- The sum of the actual DATA tests is pointwise dominated by the stopped
physical all-slot gain. The physical count includes the full calendar block. -/
theorem blockDataStaySum_le_actualBlockGain (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) (e : Coordinates p) :
    blockDataStaySum ids rewards C_star C_h eta (s := s) i e ≤
      actualBlockGain ids rewards C_star C_h eta (s := s) i e := by
  let x := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let b := ReferenceInitializationRun.run x s.val
  by_cases hc : b.crossing = none
  · have hrem : b.completed < n_boot p := by
      have hno : b.crossing.isSome ≠ true := by rw [hc]; simp
      have hcompleted :=
        (ReferenceInitializationRun.run_progress x s.val s.isLt.le).resolve_left hno
      rw [hcompleted]
      exact s.isLt
    by_cases hi : i ∈ ReferenceInitializationRun.uninformed b
    · let y := ReferenceInitializationRun.physical x b hrem
      let j : {j // j ∈ y.uninformed} :=
        ⟨i, by change i ∈ ReferenceInitializationRun.uninformed b; exact hi⟩
      have hnext : ReferenceInitializationRun.nextBlock b hrem = s := by
        simpa [x, b] using
          (GeneratedBootstrapRoundLaw.processed_nextBlock ids rewards C_star C_h eta s e
            (by simpa [x, b] using hc) hrem)
      have hsum :
          (∑ t ∈ calendarBlock p s,
            GeneratedStayConditionalMean.actualDataStayTest p ids rewards C_star C_h eta
              (s := s) t i e) ≤
          ∑ t ∈ calendarBlock p s,
            if y.active j = true ∧ t ∈ BootstrapPhysicalBlock.physicalStayRounds y j
            then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro t ht
        have hterm := actualDataStayTest_le_physicalStayIndicator ids rewards C_star C_h eta
          (s := s) i e b rfl hc hrem hi t ht
        simpa [x, y, j] using hterm
      have hgain :
          actualBlockGain ids rewards C_star C_h eta (s := s) i e =
            (BootstrapPhysicalBlock.physicalStayGain y j : ℝ) := by
        calc
          actualBlockGain ids rewards C_star C_h eta (s := s) i e =
              (BootstrapWeightPotential.effectiveGain
                (ReferenceInitializationRun.weightInput x b hrem ⟨i, hi⟩) : ℝ) :=
            actualBlockGain_eq_referenceEffectiveGain ids rewards C_star C_h eta
              (s := s) i e hc hrem hi
          _ = (BootstrapPhysicalBlock.physicalStayGain y j : ℝ) := by
            exact congrArg (fun n : ℕ => (n : ℝ))
              (ReferenceInitializationRun.weightInput_full_gain x b hrem ⟨i, hi⟩)
      calc
        blockDataStaySum ids rewards C_star C_h eta (s := s) i e =
            ∑ t ∈ calendarBlock p s,
              GeneratedStayConditionalMean.actualDataStayTest p ids rewards C_star C_h eta
                (s := s) t i e := rfl
        _ ≤ ∑ t ∈ calendarBlock p s,
              if y.active j = true ∧ t ∈ BootstrapPhysicalBlock.physicalStayRounds y j
              then (1 : ℝ) else 0 := hsum
        _ = (BootstrapPhysicalBlock.physicalStayGain y j : ℝ) :=
          by simpa [hnext] using physicalStayIndicator_sum_eq_gain y j
        _ = actualBlockGain ids rewards C_star C_h eta (s := s) i e := hgain.symm
    · have hzero : ∀ t ∈ calendarBlock p s,
          GeneratedStayConditionalMean.actualDataStayTest p ids rewards C_star C_h eta
            (s := s) t i e = 0 := by
        intro t ht
        exact actualDataStayTest_eq_zero_of_notIncoming ids rewards C_star C_h eta
          (s := s) i e b rfl hc hrem hi t
      have hsumzero : blockDataStaySum ids rewards C_star C_h eta (s := s) i e = 0 := by
        change (∑ t ∈ calendarBlock p s,
          GeneratedStayConditionalMean.actualDataStayTest p ids rewards C_star C_h eta
            (s := s) t i e) = 0
        apply Finset.sum_eq_zero
        intro t ht
        exact hzero t ht
      have hiPhysical : i ∉ (ReferenceInitializationRun.physical x b hrem).uninformed := by
        change i ∉ ReferenceInitializationRun.uninformed b
        exact hi
      have hgainzero : actualBlockGain ids rewards C_star C_h eta (s := s) i e = 0 := by
        simp [actualBlockGain, gainAtBoundary, hc, hrem, hiPhysical, x, b]
      rw [hsumzero, hgainzero]
  · have hcross : b.crossing ≠ none := hc
    have htestzero : ∀ t ∈ calendarBlock p s,
        GeneratedStayConditionalMean.actualDataStayTest p ids rewards C_star C_h eta
          (s := s) t i e = 0 := by
      intro t ht
      have hnone_t : descriptor p ids rewards C_star C_h eta s t e = none := by
        exact (GeneratedBootstrapRoundLaw.descriptor_eq_none_iff ids rewards C_star C_h eta
          s t e).2 (by simpa [b, x] using hcross)
      simp [GeneratedStayConditionalMean.actualDataStayTest,
        GeneratedBootstrapFiltration.testValue, hnone_t,
        GeneratedStayConditionalMean.dataStayTest]
    have hsumzero : blockDataStaySum ids rewards C_star C_h eta (s := s) i e = 0 := by
      change (∑ t ∈ calendarBlock p s,
        GeneratedStayConditionalMean.actualDataStayTest p ids rewards C_star C_h eta
          (s := s) t i e) = 0
      apply Finset.sum_eq_zero
      intro t ht
      exact htestzero t ht
    have hgainzero : actualBlockGain ids rewards C_star C_h eta (s := s) i e = 0 := by
      simp [actualBlockGain, gainAtBoundary, hc, x, b]
    rw [hsumzero, hgainzero]

/-- The actual per-round conditional mean, towered back to the literal
block-start filtration, retains the fixed-U lower bound on the start event. -/
theorem actualDataStayTest_condExp_ge_on_blockStartEvent (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) (a z : Fin p.K)
    (u : Fin (A_id p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s) :
    ∀ᵐ e ∂originalLaw p, e ∈ blockStartEvent ids rewards C_star C_h eta
      (s := s) i a z u →
      condExp (analysisFiltration p (blockStartRound p s).val) (originalLaw p)
        (GeneratedStayConditionalMean.actualDataStayTest p ids rewards C_star C_h eta
          (s := s) t i) e ≥
        sourceChi rewards t a * (if ids u t = false then 1 else 0) / 16 := by
  let E := blockStartEvent ids rewards C_star C_h eta (s := s) i a z u
  let f := GeneratedStayConditionalMean.actualDataStayTest p ids rewards C_star C_h eta
    (s := s) t i
  have hstartt : analysisFiltration p (blockStartRound p s).val ≤
      analysisFiltration p t.val := by
    apply (analysisFiltration p).mono
    exact (mem_calendarBlock_iff p s t).mp ht |>.1
  have hstartAmbient : analysisFiltration p (blockStartRound p s).val ≤
      (inferInstance : MeasurableSpace (Coordinates p)) := by
    change analysisFiltration p (blockStartRound p s).val ≤ _
    exact analysisFiltration_le p (blockStartRound p s).val
  have htAmbient : analysisFiltration p t.val ≤
      (inferInstance : MeasurableSpace (Coordinates p)) := by
    change analysisFiltration p t.val ≤ _
    exact analysisFiltration_le p t.val
  have hE : MeasurableSet[analysisFiltration p (blockStartRound p s).val] E := by
    simpa [E] using blockStartEvent_measurable ids rewards C_star C_h eta
      (s := s) i a z u
  have hEambient : MeasurableSet E :=
    (MeasurableSpace.le_def.mp hstartAmbient) E hE
  have hsource := GeneratedStayConditionalMean.sourceClockConditionalMean_ge_of_isolation
    p ids rewards C_star C_h eta (s := s) t i a z ht
  have hclock :
      (fun e => GeneratedStayConditionalMean.sourceClockTest p ids rewards C_star C_h eta
        (s := s) t i (GeneratedBootstrapFiltration.sourceClockIndex p t) e) = f := by
    funext e
    simpa [GeneratedBootstrapFiltration.sourceClockIndex] using
      GeneratedStayConditionalMean.sourceClockTest_at_round p ids rewards C_star C_h eta
        (s := s) t i e
  have hshift :
      BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
        (GeneratedStayConditionalMean.sourceClockTest p ids rewards C_star C_h eta
          (s := s) t i) (t.val + 1) =
      condExp (analysisFiltration p t.val) (originalLaw p) f := by
    calc
      BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
          (GeneratedStayConditionalMean.sourceClockTest p ids rewards C_star C_h eta
            (s := s) t i) (t.val + 1) =
          BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
            (GeneratedStayConditionalMean.sourceClockTest p ids rewards C_star C_h eta
              (s := s) t i) (GeneratedBootstrapFiltration.sourceClockIndex p t) := by
                simp [GeneratedBootstrapFiltration.sourceClockIndex]
      _ = condExp (analysisFiltration p t.val) (originalLaw p)
          (GeneratedStayConditionalMean.sourceClockTest p ids rewards C_star C_h eta
            (s := s) t i (GeneratedBootstrapFiltration.sourceClockIndex p t)) :=
        GeneratedBootstrapFiltration.bootstrapConditionalMean_source_shift p
          (GeneratedStayConditionalMean.sourceClockTest p ids rewards C_star C_h eta
            (s := s) t i) t
      _ = condExp (analysisFiltration p t.val) (originalLaw p) f := congrArg _ hclock
  have hctlower : ∀ᵐ e ∂originalLaw p,
      e ∈ E → condExp (analysisFiltration p t.val) (originalLaw p) f e ≥
        sourceChi rewards t a * (if ids u t = false then 1 else 0) / 16 := by
    filter_upwards [hsource] with e he
    intro hevent
    have hpersist := blockStartGuard_persists ids rewards C_star C_h eta
      (s := s) i a z u e hevent t ht
    rcases hpersist with ⟨d, hdesc, hguard⟩
    have hiso := blockStartGuard_implies_isolation ids rewards (s := s) i a z u d hguard
    have hlower := blockStartGuard_dataStayLowerBound ids rewards
      (s := s) t i a z u d hguard
    have hmean := he (by simpa [hdesc] using hiso)
    rw [hshift, hdesc, hlower] at hmean
    exact hmean
  have htestNonneg : 0 ≤ᵐ[originalLaw p] f := by
    apply Filter.Eventually.of_forall
    intro e
    change 0 ≤ GeneratedStayConditionalMean.dataStayTest p ids rewards (s := s) t i
      (descriptor p ids rewards C_star C_h eta s t e, current p t e)
    exact (GeneratedStayConditionalMean.dataStayTest_unit_bounds p ids rewards
      (s := s) t i (descriptor p ids rewards C_star C_h eta s t e, current p t e)).1
  have hctNonneg : 0 ≤ᵐ[originalLaw p]
      condExp (analysisFiltration p t.val) (originalLaw p) f :=
    condExp_nonneg htestNonneg
  let g : Coordinates p → ℝ := E.indicator fun _ =>
    sourceChi rewards t a * (if ids u t = false then 1 else 0) / 16
  have hgMeas : StronglyMeasurable[analysisFiltration p (blockStartRound p s).val] g := by
    change StronglyMeasurable[analysisFiltration p (blockStartRound p s).val] (E.indicator fun _ =>
      sourceChi rewards t a * (if ids u t = false then 1 else 0) / 16)
    exact (Measurable.indicator measurable_const hE).stronglyMeasurable
  have hgInt : Integrable g (originalLaw p) := by
    change Integrable (E.indicator fun _ =>
      sourceChi rewards t a * (if ids u t = false then 1 else 0) / 16) (originalLaw p)
    exact (integrable_indicator_iff (μ := originalLaw p) hEambient).2
      (integrable_const
        (sourceChi rewards t a * (if ids u t = false then 1 else 0) / 16)).integrableOn
  have hg_le_ct : g ≤ᵐ[originalLaw p]
      condExp (analysisFiltration p t.val) (originalLaw p) f := by
    filter_upwards [hctlower, hctNonneg] with e hlow hnonneg
    by_cases hevent : e ∈ E
    · simpa [g, hevent] using hlow
    · simpa [g, hevent] using hnonneg
  have hmono : condExp (analysisFiltration p (blockStartRound p s).val)
      (originalLaw p) g ≤ᵐ[originalLaw p]
      condExp (analysisFiltration p (blockStartRound p s).val) (originalLaw p)
        (condExp (analysisFiltration p t.val) (originalLaw p) f) :=
    condExp_mono (m := analysisFiltration p (blockStartRound p s).val)
      hgInt integrable_condExp hg_le_ct
  have hgeq : condExp (analysisFiltration p (blockStartRound p s).val)
      (originalLaw p) g =ᵐ[originalLaw p] g :=
    Filter.Eventually.of_forall (fun e => congrFun
      (condExp_of_stronglyMeasurable (hm := hstartAmbient) (hf := hgMeas)
        (hfi := hgInt)) e)
  have htower := condExp_condExp_of_le (hm₁₂ := hstartt) (hm₂ := htAmbient)
    (f := f) (μ := originalLaw p)
  filter_upwards [hmono, hgeq, htower] with e hmono_e hgeq_e htower_e
  intro hevent
  have hfinal : g e ≤ condExp (analysisFiltration p (blockStartRound p s).val)
      (originalLaw p) f e := by
    calc
      g e = condExp (analysisFiltration p (blockStartRound p s).val)
          (originalLaw p) g e := hgeq_e.symm
      _ ≤ condExp (analysisFiltration p (blockStartRound p s).val) (originalLaw p)
          (condExp (analysisFiltration p t.val) (originalLaw p) f) e := hmono_e
      _ = condExp (analysisFiltration p (blockStartRound p s).val)
          (originalLaw p) f e := htower_e
  simpa [g, E, hevent] using hfinal

/-- The eventwise full-block gain bound before averaging the original private
ID. It applies the finite conditional-expectation tower at the literal block
start, then integrates over any measurable subset of the structural event. -/
theorem actualBlockGain_setIntegral_ge_on_blockStartEvent (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    {s : Fin (n_boot p)} (i : Follower p.m) (a z : Fin p.K)
    (u : Fin (A_id p)) (A : Set (Coordinates p))
    (hA : MeasurableSet[analysisFiltration p (blockStartRound p s).val] A)
    (hAsub : A ⊆ blockStartEvent ids rewards C_star C_h eta
      (s := s) i a z u) :
    ∫ e in A, actualBlockGain ids rewards C_star C_h eta (s := s) i e ∂originalLaw p ≥
      (∑ t ∈ calendarBlock p s,
        sourceChi rewards t a * (if ids u t = false then 1 else 0) / 16) *
        (originalLaw p).real A := by
  let E := blockStartEvent ids rewards C_star C_h eta (s := s) i a z u
  let f : Fin p.T → Coordinates p → ℝ := fun t e =>
    GeneratedStayConditionalMean.actualDataStayTest p ids rewards C_star C_h eta
      (s := s) t i e
  let c := blockStartGainCoefficient ids rewards (s := s) a u
  have hstartAmbient : analysisFiltration p (blockStartRound p s).val ≤
      (inferInstance : MeasurableSpace (Coordinates p)) := by
    change analysisFiltration p (blockStartRound p s).val ≤ _
    exact analysisFiltration_le p (blockStartRound p s).val
  have hE : MeasurableSet[analysisFiltration p (blockStartRound p s).val] E := by
    simpa [E] using blockStartEvent_measurable ids rewards C_star C_h eta
      (s := s) i a z u
  have hAambient : MeasurableSet A :=
    (MeasurableSpace.le_def.mp hstartAmbient) A hA
  have htestsInt : ∀ t ∈ calendarBlock p s, Integrable (f t) (originalLaw p) := by
    intro t ht
    exact GeneratedStayConditionalMean.integrable_actualDataStayTest p ids rewards
      C_star C_h eta (s := s) t i ht
  have hsumInt : Integrable (blockDataStaySum ids rewards C_star C_h eta
      (s := s) i) (originalLaw p) := by
    apply integrable_finsetSum
    intro t ht
    exact htestsInt t ht
  have hgainInt := integrable_actualBlockGain ids rewards C_star C_h eta
    (s := s) i
  have hsumFn : blockDataStaySum ids rewards C_star C_h eta (s := s) i =
      ∑ t ∈ calendarBlock p s, f t := by
    funext e
    simp [blockDataStaySum, f, Finset.sum_apply]
  have hpoint : ∀ e, blockDataStaySum ids rewards C_star C_h eta (s := s) i e ≤
      actualBlockGain ids rewards C_star C_h eta (s := s) i e := by
    intro e
    exact blockDataStaySum_le_actualBlockGain ids rewards C_star C_h eta
      (s := s) i e
  have hcondSum :
      condExp (analysisFiltration p (blockStartRound p s).val) (originalLaw p)
        (blockDataStaySum ids rewards C_star C_h eta
        (s := s) i) =ᵐ[originalLaw p]
        fun e => ∑ t ∈ calendarBlock p s,
          condExp (analysisFiltration p (blockStartRound p s).val)
            (originalLaw p) (f t) e := by
    rw [hsumFn]
    have hraw := condExp_finsetSum (μ := originalLaw p) (s := calendarBlock p s)
      (f := f) htestsInt (analysisFiltration p (blockStartRound p s).val)
    filter_upwards [hraw] with e he
    simpa only [Finset.sum_apply] using he
  have hroundLower : ∀ᵐ e ∂originalLaw p,
      e ∈ E → ∀ t ∈ calendarBlock p s,
        condExp (analysisFiltration p (blockStartRound p s).val)
          (originalLaw p) (f t) e ≥
          sourceChi rewards t a * (if ids u t = false then 1 else 0) / 16 := by
    filter_upwards [(calendarBlock p s).eventually_all.mpr (fun t ht => by
      simpa only [f, E] using actualDataStayTest_condExp_ge_on_blockStartEvent
        ids rewards C_star C_h eta (s := s) i a z u t ht)] with e he
    intro hevent t ht
    exact he t ht hevent
  have hsumLower : ∀ᵐ e ∂originalLaw p,
      e ∈ E → c ≤ ∑ t ∈ calendarBlock p s,
        condExp (analysisFiltration p (blockStartRound p s).val)
          (originalLaw p) (f t) e := by
    filter_upwards [hroundLower] with e he
    intro hevent
    dsimp [c, blockStartGainCoefficient]
    apply Finset.sum_le_sum
    intro t ht
    exact he hevent t ht
  have hcondSumLower : ∀ᵐ e ∂originalLaw p,
      e ∈ E → c ≤ condExp (analysisFiltration p (blockStartRound p s).val) (originalLaw p)
        (blockDataStaySum ids rewards C_star C_h eta (s := s) i) e := by
    filter_upwards [hcondSum, hsumLower] with e heq hlow
    intro hevent
    rw [heq]
    exact hlow hevent
  have hcondMono : condExp (analysisFiltration p (blockStartRound p s).val) (originalLaw p)
      (blockDataStaySum ids rewards C_star C_h eta (s := s) i) ≤ᵐ[originalLaw p]
      condExp (analysisFiltration p (blockStartRound p s).val) (originalLaw p)
        (actualBlockGain ids rewards C_star C_h eta (s := s) i) :=
    condExp_mono (m := analysisFiltration p (blockStartRound p s).val) hsumInt hgainInt
      (Filter.Eventually.of_forall hpoint)
  have hcondGainLower : ∀ᵐ e ∂originalLaw p,
      e ∈ E → c ≤ condExp (analysisFiltration p (blockStartRound p s).val) (originalLaw p)
        (actualBlockGain ids rewards C_star C_h eta (s := s) i) e := by
    filter_upwards [hcondMono, hcondSumLower] with e hmono hlow
    intro hevent
    exact le_trans (hlow hevent) hmono
  have hlocal : ∀ᵐ e ∂originalLaw p,
      e ∈ A → c ≤ condExp (analysisFiltration p (blockStartRound p s).val) (originalLaw p)
        (actualBlockGain ids rewards C_star C_h eta (s := s) i) e := by
    filter_upwards [hcondGainLower] with e he
    intro heA
    exact he (hAsub heA)
  have hconst : ∫ e in A, (fun _ : Coordinates p => c) e ∂originalLaw p =
      c * (originalLaw p).real A := by
    rw [setIntegral_const]
    simp [smul_eq_mul, mul_comm]
  have hmonoIntegral :
      ∫ e in A, (fun _ : Coordinates p => c) e ∂originalLaw p ≤
        ∫ e in A, condExp (analysisFiltration p (blockStartRound p s).val) (originalLaw p)
          (actualBlockGain ids rewards C_star C_h eta (s := s) i) e ∂originalLaw p :=
    setIntegral_mono_on_ae (integrable_const c).integrableOn
      integrable_condExp.integrableOn hAambient hlocal
  have htower := setIntegral_condExp hstartAmbient hgainInt hA
  calc
    ∫ e in A, actualBlockGain ids rewards C_star C_h eta (s := s) i e ∂originalLaw p
        = ∫ e in A, condExp (analysisFiltration p (blockStartRound p s).val) (originalLaw p)
            (actualBlockGain ids rewards C_star C_h eta (s := s) i) e ∂originalLaw p :=
          htower.symm
    _ ≥ c * (originalLaw p).real A := by
      rw [← hconst]
      exact hmonoIntegral
    _ = (∑ t ∈ calendarBlock p s,
          sourceChi rewards t a * (if ids u t = false then 1 else 0) / 16) *
          (originalLaw p).real A := by
      rfl


end Bandits.Support.GeneratedStayBlockTower

end
