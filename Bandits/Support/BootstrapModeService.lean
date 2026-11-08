/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPhysicalBlock
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.ContinuousLearningRows
public import Bandits.Support.PublicDiscreteDraws
public import Bandits.Support.BootstrapBlockIsolation
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.UniformOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# One-round physical bootstrap service

The physical event predicates below evaluate the existing bootstrap actions
and feedback after replacing only one round's complete-row coordinates and
fresh finite private draw values.  They do not construct a second protocol or
make a claim about conditional histories or integrated block gain.

Sources: `sources/zip4/manuscript/07_public_setup.tex:74-103` and
`sources/zip4/manuscript/appendix_b_communication.tex:398-445`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.BootstrapModeService

open ConstructorDimensions BootstrapDimensions FiniteBanditModel
open BootstrapPhysicalBlock CompletePublicTable ContinuousLearningRows
open PublicDiscreteDraws
open MeasureTheory ProbabilityTheory
open scoped BigOperators

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : ConstructorDimensions.Parameters} {s : Fin (n_boot p)}

/-- The current-time part of one already existing complete row. -/
abbrev RoundForward (p : ConstructorDimensions.Parameters) := Fin (A_id p) → Bool

/-- The complete-row coordinates read by the physical policy in one round:
the current forward-bit vector and the existing continuous time-control. -/
abbrev RoundCoordinates (p : ConstructorDimensions.Parameters) :=
  RoundForward p × ContinuousLearningRows.TimeControl p

/-- Extract only time `t` from an existing complete row. -/
def roundCoordinates (p : ConstructorDimensions.Parameters) (t : Fin p.T)
    (r : CompletePublicTable.CompleteRow p) : RoundCoordinates p :=
  (fun u => r.1 u t, r.2 t)

/-- The accepted one-round factor of the complete-row law. -/
def roundForwardMeasure (p : ConstructorDimensions.Parameters) : Measure (RoundForward p) :=
  Measure.pi (fun _ : Fin (A_id p) => CompletePublicTable.forwardBitLaw p)

/-- Product law of current forward bits and current continuous controls. -/
def roundCoordinatesMeasure (p : ConstructorDimensions.Parameters) : Measure (RoundCoordinates p) :=
  (roundForwardMeasure p).prod (ContinuousLearningRows.timeControlLaw p)

instance roundForwardMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (roundForwardMeasure p) := by
  unfold roundForwardMeasure
  infer_instance

instance roundCoordinatesMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (roundCoordinatesMeasure p) := by
  unfold roundCoordinatesMeasure
  infer_instance

/-- The current-time event that every bit in the coordinator's retained list
is true.  An empty list satisfies this product event by the empty-product
convention; multicast service bounds separately require actual membership. -/
def forwardReleaseSet (p : ConstructorDimensions.Parameters)
    (list : Finset (Fin (A_id p))) : Set (RoundForward p) :=
  (list : Set (Fin (A_id p))).pi (fun _ => ({true} : Set Bool))

/-- Under the accepted one-round forward-bit product marginal, the mass of
release is exactly the full-list product, including the empty-list case. -/
theorem forwardRelease_mass (p : ConstructorDimensions.Parameters)
    (list : Finset (Fin (A_id p))) :
    (roundForwardMeasure p).real (forwardReleaseSet p list) =
      (1 - 1 / (L0 p : ℝ)) ^ list.card := by
  classical
  rw [Measure.real, roundForwardMeasure, forwardReleaseSet,
    Measure.pi_pi_finset, ENNReal.toReal_prod]
  calc
    (∏ u ∈ list, ((CompletePublicTable.forwardBitLaw p) {true}).toReal) =
        ∏ _u ∈ list, (1 - 1 / (L0 p : ℝ)) := by
      apply Finset.prod_congr rfl
      intro u hu
      simpa [Measure.real] using CompletePublicTable.forwardBitLaw_true_mass p
    _ = (1 - 1 / (L0 p : ℝ)) ^ list.card := by simp

private theorem dyadic_no_collision_ge_quarter (q : ℕ) :
    1 ≤ q → (1 / 4 : ℝ) ≤ (1 - 1 / (2 ^ q : ℝ)) ^ (2 ^ q) := by
  induction q with
  | zero => intro hq; omega
  | succ q ih =>
      intro hq
      cases q with
      | zero => norm_num
      | succ q =>
          have hprev := ih (by omega : 1 ≤ q + 1)
          let n : ℕ := 2 ^ (q + 1)
          let a : ℝ := 1 - 1 / (n : ℝ)
          let b : ℝ := 1 - 1 / ((2 * n : ℕ) : ℝ)
          have hnpos : 0 < n := by simp [n]
          have hn1 : 1 ≤ n := Nat.succ_le_of_lt hnpos
          have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
          have ha0 : 0 ≤ a := by
            dsimp [a]
            have hinv : 1 / (n : ℝ) ≤ 1 :=
              by simpa using one_div_le_one_div_of_le (by norm_num) hnreal
            linarith
          have ha1 : a ≤ 1 := by
            dsimp [a]
            have hinv : 0 ≤ 1 / (n : ℝ) := by positivity
            linarith
          have hratio : b = (1 + a) / 2 := by
            dsimp [a, b]
            push_cast
            field_simp
            ring
          have hsq : a ≤ b ^ 2 := by
            rw [hratio]
            nlinarith [sq_nonneg (1 - a)]
          have hpow : a ^ n ≤ (b ^ 2) ^ n :=
            pow_le_pow_left₀ ha0 hsq n
          have hexp : 2 ^ (q + 2) = 2 * n := by
            simp [n, pow_succ, Nat.mul_comm]
          have hbase : b = 1 - 1 / (2 ^ (q + 2) : ℝ) := by
            dsimp [b]
            have hcast : ((2 * n : ℕ) : ℝ) = (2 ^ (q + 2) : ℝ) := by
              exact_mod_cast hexp.symm
            rw [hcast]
          have hrewrite : (b ^ 2) ^ n =
              (1 - 1 / (2 ^ (q + 2) : ℝ)) ^ (2 ^ (q + 2)) := by
            calc
              (b ^ 2) ^ n = b ^ (2 * n) := by rw [pow_mul]
              _ = (1 - 1 / (2 ^ (q + 2) : ℝ)) ^ (2 ^ (q + 2)) := by
                rw [← hexp, ← hbase]
          have hprev' : (1 / 4 : ℝ) ≤ a ^ n := by
            simpa [a, n] using hprev
          exact hprev'.trans (hpow.trans_eq hrewrite)

/-- The source dyadic cutoff retains at least one quarter of the complete
forward-bit product, including every listed bit. -/
theorem forwardRelease_ge_quarter (p : ConstructorDimensions.Parameters)
    (list : Finset (Fin (A_id p))) (hcard : list.card ≤ L0 p) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (L0 p : ℝ)) ^ list.card := by
  have hq : 1 ≤ Nat.clog 2 (2 * b_N p) :=
    Nat.clog_pos (by decide) (by have hb := ConstructorDimensions.b_N_pos p; omega)
  have hdyad := dyadic_no_collision_ge_quarter (Nat.clog 2 (2 * b_N p)) hq
  have hb : 1 ≤ b_N p := Nat.succ_le_of_lt (ConstructorDimensions.b_N_pos p)
  have h2b : 2 ≤ 2 * b_N p := by omega
  have hLtwo : 2 ≤ L0 p :=
    h2b.trans (BootstrapDimensions.two_mul_b_N_le_L0 p)
  have hbase0 : 0 ≤ 1 - 1 / (L0 p : ℝ) := by
    have hLnat : 1 ≤ L0 p := by omega
    have hL : (1 : ℝ) ≤ (L0 p : ℝ) := by exact_mod_cast hLnat
    have hinv : 1 / (L0 p : ℝ) ≤ 1 :=
      by simpa using one_div_le_one_div_of_le (by norm_num) hL
    linarith
  have hbase1 : 1 - 1 / (L0 p : ℝ) ≤ 1 := by
    have hinv : 0 ≤ 1 / (L0 p : ℝ) := by positivity
    linarith
  have hlarge : (1 / 4 : ℝ) ≤ (1 - 1 / (L0 p : ℝ)) ^ L0 p := by
    simpa [BootstrapDimensions.L0] using hdyad
  exact hlarge.trans (pow_le_pow_of_le_one hbase0 hbase1 hcard)

def roundSlice (r : RoundCoordinates p) : ContinuousControlSlice.Slice p.m p.K :=
  r.2.1

theorem measurePreserving_roundSlice (p : ConstructorDimensions.Parameters) :
    MeasurePreserving roundSlice (roundCoordinatesMeasure p)
      (ContinuousControlSlice.sliceLaw p.m p.K) := by
  have hcontrol : MeasurePreserving (Prod.snd : RoundCoordinates p →
      ContinuousLearningRows.TimeControl p) (roundCoordinatesMeasure p)
      (ContinuousLearningRows.timeControlLaw p) := measurePreserving_snd
  exact (ContinuousLearningRows.measurePreserving_slice p).comp hcontrol

def roundSlot (r : RoundCoordinates p) : PublicDiscreteDraws.Slot :=
  PublicDiscreteDraws.slotDraw (roundSlice r)

theorem measurePreserving_roundSlot (p : ConstructorDimensions.Parameters) :
    MeasurePreserving (roundSlot (p := p)) (roundCoordinatesMeasure p)
      PublicDiscreteDraws.slotPMF.toMeasure := by
  exact (PublicDiscreteDraws.measurePreserving_slotDraw).comp
    (measurePreserving_roundSlice p)

theorem round_data_mass (p : ConstructorDimensions.Parameters) :
    (roundCoordinatesMeasure p) (roundSlot (p := p) ⁻¹' {PublicDiscreteDraws.dataSlot}) =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  let h := measurePreserving_roundSlot p
  calc
    (roundCoordinatesMeasure p) (roundSlot (p := p) ⁻¹' {PublicDiscreteDraws.dataSlot}) =
        ((roundCoordinatesMeasure p).map (roundSlot (p := p)))
          {PublicDiscreteDraws.dataSlot} :=
            (Measure.map_apply h.measurable (measurableSet_singleton _)).symm
    _ = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [h.map_eq]
      simp [PublicDiscreteDraws.slotPMF, PublicDiscreteDraws.slotMass_data,
        ContinuousCategorical.massPMF_apply]

theorem round_data_mass_real (p : ConstructorDimensions.Parameters) :
    (roundCoordinatesMeasure p).real
      (roundSlot (p := p) ⁻¹' {PublicDiscreteDraws.dataSlot}) = 1 / 2 := by
  rw [Measure.real, round_data_mass]
  norm_num

/-- A genuine arm-complement subtype is nonempty because the accepted arm
count is at least two. -/
theorem avoidArm_nonempty {K : ℕ} (hK : 2 ≤ K) (a : Fin K) :
    Nonempty {b : Fin K // b ≠ a} := by
  by_cases ha : a.val = 0
  · refine ⟨⟨⟨1, by omega⟩, ?_⟩⟩
    intro h
    have hv := congrArg Fin.val h
    simp [ha] at hv
  · refine ⟨⟨⟨0, by omega⟩, ?_⟩⟩
    intro h
    apply ha
    have hv := congrArg Fin.val h
    exact hv.symm

/-- Current one-round private source draws: one independent uniform arm value
per player, one genuine coordinator complement value, and one genuine held-arm
complement value for each uninformed follower. -/
abbrev RoundPrivateValues (x : BootstrapPhysicalBlock.Input p s) :=
  (Player p.m → Arm p.K) ×
    (BootstrapPhysicalBlock.AvoidArm p x.target ×
      ((j : {j // j ∈ x.uninformed}) → BootstrapPhysicalBlock.AvoidArm p (x.held j)))

/-- The accepted equal-mass finite arm law, used for one-round private uniform
arm VALUES only. -/
def privateArmMeasure (p : ConstructorDimensions.Parameters) : Measure (Arm p.K) :=
  (PublicDiscreteDraws.pilotPMF p.K (K_pos p)).toMeasure

instance privateArmMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (privateArmMeasure p) := by
  unfold privateArmMeasure
  infer_instance

theorem privateArm_noncollision_mass (p : ConstructorDimensions.Parameters)
    (a : Arm p.K) :
    privateArmMeasure p {b : Arm p.K | b ≠ a} =
      ENNReal.ofReal (1 - 1 / (p.K : ℝ)) := by
  have hsingle : privateArmMeasure p {a} = ENNReal.ofReal (1 / (p.K : ℝ)) := by
    rw [privateArmMeasure, PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a)]
    simp [PublicDiscreteDraws.pilotPMF, ContinuousCategorical.massPMF_apply,
      PublicDiscreteDraws.equalMass]
  have hset : ({b : Arm p.K | b ≠ a} : Set (Arm p.K)) = ({a} : Set (Arm p.K))ᶜ := by
    ext b
    simp
  rw [hset, measure_compl (measurableSet_singleton a) (measure_ne_top _ _),
    measure_univ, hsingle]
  rw [← ENNReal.ofReal_one]
  rw [← ENNReal.ofReal_sub (1 : ℝ) (by positivity)]

/-- Independent one-round uniform private arm values for all player labels. -/
def privateArmVectorMeasure (p : ConstructorDimensions.Parameters) :
    Measure (Player p.m → Arm p.K) :=
  Measure.pi (fun _ : Player p.m => privateArmMeasure p)

instance privateArmVectorMeasure_probability (p : ConstructorDimensions.Parameters) :
    IsProbabilityMeasure (privateArmVectorMeasure p) := by
  unfold privateArmVectorMeasure
  infer_instance

def publicPilotVectorOnSlice (p : ConstructorDimensions.Parameters)
    (u : ContinuousControlSlice.Slice p.m p.K) : Player p.m → Arm p.K :=
  fun i => PublicDiscreteDraws.pilotDraw (K_pos p) i u

/-- The accepted public pilot maps have their full independent product law on
one continuous slice. -/
theorem measurePreserving_publicPilotVectorOnSlice (p : ConstructorDimensions.Parameters) :
    MeasurePreserving (publicPilotVectorOnSlice p)
      (ContinuousControlSlice.sliceLaw p.m p.K) (privateArmVectorMeasure p) := by
  classical
  let label : Player p.m → ContinuousControlSlice.Label p.m p.K :=
    fun i => ContinuousControlSlice.Label.pilot i
  have hinj : Function.Injective label := by
    intro i j hij
    exact Sum.inl_injective (Sum.inr_injective (Sum.inr_injective hij))
  have hcoords := (ContinuousControlSlice.iIndepFun_coordinate p.m p.K).precomp
    (g := label) hinj
  have hpilots := hcoords.comp
    (fun i => PublicDiscreteDraws.pilotFromScalar p.K (K_pos p))
    (fun i => by
      change Measurable (PublicDiscreteDraws.drawFromScalar
        p.two_le_m p.m_lt_K (K_pos p) (.pilot i))
      exact PublicDiscreteDraws.measurable_drawFromScalar
        p.two_le_m p.m_lt_K (K_pos p) (.pilot i))
  refine ⟨measurable_pi_iff.mpr (fun i => PublicDiscreteDraws.measurable_pilotDraw
    (K_pos p) i), ?_⟩
  have hmap := hpilots.map_fun_eq_pi_map
    (fun i => (PublicDiscreteDraws.measurable_pilotDraw (K_pos p) i).aemeasurable)
  change (ContinuousControlSlice.sliceLaw p.m p.K).map
      (fun u : ContinuousControlSlice.Slice p.m p.K => fun i : Player p.m =>
        PublicDiscreteDraws.pilotDraw (K_pos p) i u) =
    Measure.pi (fun i : Player p.m =>
      (PublicDiscreteDraws.pilotPMF p.K (K_pos p)).toMeasure)
  calc
    (ContinuousControlSlice.sliceLaw p.m p.K).map
        (fun u : ContinuousControlSlice.Slice p.m p.K => fun i : Player p.m =>
          PublicDiscreteDraws.pilotDraw (K_pos p) i u) =
        Measure.pi (fun i : Player p.m =>
          (ContinuousControlSlice.sliceLaw p.m p.K).map
            (PublicDiscreteDraws.pilotDraw (K_pos p) i)) := hmap
    _ = Measure.pi (fun _ : Player p.m =>
        (PublicDiscreteDraws.pilotPMF p.K (K_pos p)).toMeasure) := by
      congr 1
      funext i
      exact PublicDiscreteDraws.map_pilotDraw (K_pos p) i

/-- The public pilot vector under the current-coordinate marginal is exactly
the same independent finite arm product as the auxiliary private values. -/
theorem measurePreserving_roundPublicPilotVector (p : ConstructorDimensions.Parameters) :
    MeasurePreserving (fun r : RoundCoordinates p => publicPilotVectorOnSlice p (roundSlice r))
      (roundCoordinatesMeasure p) (privateArmVectorMeasure p) :=
  (measurePreserving_publicPilotVectorOnSlice p).comp (measurePreserving_roundSlice p)

def privateArmAvoidanceSet (p : ConstructorDimensions.Parameters)
    (I : Finset (Player p.m)) (a : Arm p.K) : Set (Player p.m → Arm p.K) :=
  (I : Set (Player p.m)).pi (fun _ => {b : Arm p.K | b ≠ a})

/-- Exact product-coordinate avoidance mass for any fixed collection of the
auxiliary private uniform arm values. -/
theorem privateArmVectorAvoidance_mass (p : ConstructorDimensions.Parameters)
    (I : Finset (Player p.m)) (a : Arm p.K) :
    (privateArmVectorMeasure p).real (privateArmAvoidanceSet p I a) =
      (1 - 1 / (p.K : ℝ)) ^ I.card := by
  classical
  have hKone : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (K_pos p))
  have hrecip : 1 / (p.K : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hKone
  have hbase : 0 ≤ 1 - 1 / (p.K : ℝ) := by linarith
  rw [Measure.real, privateArmVectorMeasure, privateArmAvoidanceSet,
    Measure.pi_pi_finset, ENNReal.toReal_prod]
  calc
    ∏ i ∈ I, ((privateArmMeasure p) {b : Arm p.K | b ≠ a}).toReal =
        ∏ _i ∈ I, (1 - 1 / (p.K : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [privateArm_noncollision_mass]
      exact ENNReal.toReal_ofReal hbase
    _ = (1 - 1 / (p.K : ℝ)) ^ I.card := by simp

/-- A uniform value on the true complement-arm subtype. -/
def privateAvoidMeasure (p : ConstructorDimensions.Parameters) (a : Arm p.K) :
    Measure (BootstrapPhysicalBlock.AvoidArm p a) :=
  ProbabilityTheory.uniformOn (Set.univ : Set (BootstrapPhysicalBlock.AvoidArm p a))

instance privateAvoidMeasure_probability (p : ConstructorDimensions.Parameters)
    (a : Arm p.K) : IsProbabilityMeasure (privateAvoidMeasure p a) := by
  have hK : 2 ≤ p.K := p.two_le_m.trans (Nat.le_of_lt p.m_lt_K)
  unfold privateAvoidMeasure
  apply ProbabilityTheory.isProbabilityMeasure_uniformOn' Set.finite_univ ?_
    MeasurableSet.univ
  rcases avoidArm_nonempty hK a with ⟨b⟩
  exact ⟨b, Set.mem_univ _⟩

/-- Product law of independent one-round private arm and avoidance values. -/
def roundPrivateMeasure (x : BootstrapPhysicalBlock.Input p s) :
    Measure (RoundPrivateValues x) :=
  (privateArmVectorMeasure p).prod
    ((privateAvoidMeasure p x.target).prod
      (Measure.pi (fun j => privateAvoidMeasure p (x.held j))))

instance roundPrivateMeasure_probability (x : BootstrapPhysicalBlock.Input p s) :
    IsProbabilityMeasure (roundPrivateMeasure x) := by
  unfold roundPrivateMeasure
  infer_instance

/-- The physical current-snapshot experiment resamples only the current
complete-row coordinates and an independent one-round product of finite
private values. -/
def currentSnapshotMeasure (x : BootstrapPhysicalBlock.Input p s) (_t : Fin p.T) :
    Measure (RoundCoordinates p × RoundPrivateValues x) :=
  (roundCoordinatesMeasure p).prod (roundPrivateMeasure x)

instance currentSnapshotMeasure_probability (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) : IsProbabilityMeasure (currentSnapshotMeasure x t) := by
  unfold currentSnapshotMeasure
  infer_instance

/-- The forward-bit current-time projection has the literal product marginal
already specified by the complete-row construction. -/
theorem map_forwardRoundCoordinates (p : ConstructorDimensions.Parameters) (t : Fin p.T) :
    (CompletePublicTable.forwardRowMeasure p).map
        (fun f : CompletePublicTable.ForwardRow p => fun u => f u t) =
      roundForwardMeasure p := by
  classical
  have hinj : Function.Injective (fun u : Fin (A_id p) => (u, t)) := by
    intro u v huv
    exact congrArg Prod.fst huv
  have h := (CompletePublicTable.iIndepFun_forwardRowCoordinate p).precomp
    (g := fun u : Fin (A_id p) => (u, t)) hinj
  have hmeas : ∀ u : Fin (A_id p),
      AEMeasurable (CompletePublicTable.forwardRowCoordinate p u t)
        (CompletePublicTable.forwardRowMeasure p) := by
    intro u
    exact (CompletePublicTable.measurable_forwardRowCoordinate p u t).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hmeas] at h
  change (CompletePublicTable.forwardRowMeasure p).map
      (fun f u => f u t) =
    Measure.pi (fun u : Fin (A_id p) =>
      (CompletePublicTable.forwardRowMeasure p).map
        (CompletePublicTable.forwardRowCoordinate p u t)) at h
  simpa [roundForwardMeasure, CompletePublicTable.forwardRowCoordinate,
    CompletePublicTable.forwardRowCoordinate_map] using h

/-- Resampling a round uses exactly the current-time projection of the
integrated complete-row law. -/
theorem map_roundCoordinates (p : ConstructorDimensions.Parameters) (t : Fin p.T) :
    (CompletePublicTable.completeRowMeasure p).map (roundCoordinates p t) =
      roundCoordinatesMeasure p := by
  classical
  rw [CompletePublicTable.completeRowMeasure]
  change
    ((CompletePublicTable.forwardRowMeasure p).prod
      (ContinuousLearningRows.learningRowLaw p)).map
        (Prod.map (fun f => fun u => f u t) (fun r => r t)) = _
  have hf : MeasurePreserving (fun f : CompletePublicTable.ForwardRow p =>
      fun u => f u t) (CompletePublicTable.forwardRowMeasure p)
      (roundForwardMeasure p) :=
    ⟨measurable_pi_iff.mpr (fun u =>
        (measurable_pi_apply t).comp (measurable_pi_apply u)),
      map_forwardRoundCoordinates p t⟩
  have hg := ContinuousLearningRows.measurePreserving_controlAt (p := p) t
  exact (MeasurePreserving.prod hf hg).map_eq

/-- Source support indicator for the fixed rounded reward table. -/
def chi (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T)
    (a : Arm p.K) : ℝ :=
  if 0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (x.rewards t a)
  then 1 else 0

/-- The fixed input data and a single resampled current round.  All fields
except the current complete-row coordinate and current private draw values
remain those of `x`. -/
def currentInput (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T)
    (r : RoundCoordinates p)
    (uniformArms : Player p.m → Arm p.K)
    (coordinatorAvoid : BootstrapPhysicalBlock.AvoidArm p x.target)
    (followerAvoid : (j : {j // j ∈ x.uninformed}) →
      BootstrapPhysicalBlock.AvoidArm p (x.held j)) :
    BootstrapPhysicalBlock.Input p s :=
  { x with
    row :=
      (fun u q => if q = t then r.1 u else x.row.1 u q,
       fun q => if q = t then r.2 else x.row.2 q)
    uniform := fun i q => if q = t then uniformArms i else x.uniform i q
    coordinatorAvoid := fun q => if q = t then coordinatorAvoid else x.coordinatorAvoid q
    followerAvoid := fun j q => if q = t then followerAvoid j else x.followerAvoid j q }

/-- Insert current private values into the existing physical input. -/
def currentInputOf (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T)
    (r : RoundCoordinates p) (d : RoundPrivateValues x) :
    BootstrapPhysicalBlock.Input p s :=
  currentInput x t r d.1 d.2.1 d.2.2

/-- The current pre-choice mode and list are supplied by the existing state. -/
def discoveryIndicator (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (r : RoundCoordinates p) (d : RoundPrivateValues x) : ℝ :=
  if st.mode = .discover ∧
      BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = PublicDiscreteDraws.dataSlot ∧
      0 < BootstrapPhysicalBlock.feedback (currentInputOf x t r d) st t
        (ActiveRoundActions.coordinator p.two_le_m)
  then 1 else 0

/-- The multicast service indicator includes the source's explicit ID-zero
event; list membership and the list-size cutoff are conditional hypotheses of
the service lower bound, not fallback branches in this indicator. -/
def multicastIndicator (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed})
    (r : RoundCoordinates p) (d : RoundPrivateValues x) : ℝ :=
  if st.mode = .multicast ∧
      BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = PublicDiscreteDraws.dataSlot ∧
      x.ids (x.privateId j) t = false ∧
      0 < BootstrapPhysicalBlock.feedback (currentInputOf x t r d) st t
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.val)
  then 1 else 0

/-- The one-clock score from the two disjoint physical modes. -/
def oneClock (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed})
    (r : RoundCoordinates p) (d : RoundPrivateValues x) : ℝ :=
  discoveryIndicator x st t r d / 8 + multicastIndicator x st t j r d

theorem discoveryIndicator_nonneg (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (r : RoundCoordinates p) (d : RoundPrivateValues x) :
    0 ≤ discoveryIndicator x st t r d := by
  unfold discoveryIndicator
  split_ifs <;> norm_num

theorem discoveryIndicator_le_one (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (r : RoundCoordinates p) (d : RoundPrivateValues x) :
    discoveryIndicator x st t r d ≤ 1 := by
  unfold discoveryIndicator
  split_ifs <;> norm_num

theorem multicastIndicator_nonneg (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (r : RoundCoordinates p)
    (d : RoundPrivateValues x) : 0 ≤ multicastIndicator x st t j r d := by
  unfold multicastIndicator
  split_ifs <;> norm_num

theorem multicastIndicator_le_one (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (r : RoundCoordinates p)
    (d : RoundPrivateValues x) : multicastIndicator x st t j r d ≤ 1 := by
  unfold multicastIndicator
  split_ifs <;> norm_num

/-- The source clock is bounded pointwise, including the empty-list case;
the multicast probability theorem separately requires actual list membership. -/
theorem oneClock_mem_Icc (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (r : RoundCoordinates p)
    (d : RoundPrivateValues x) : oneClock x st t j r d ∈ Set.Icc (0 : ℝ) 1 := by
  cases hm : st.mode with
  | discover =>
      simp [oneClock, discoveryIndicator, multicastIndicator, hm, Set.mem_Icc]
      split_ifs <;> norm_num
  | multicast =>
      simp [oneClock, discoveryIndicator, multicastIndicator, hm, Set.mem_Icc]
      split_ifs <;> norm_num

/-- During DATA DISCOVER the coordinator's actual action is the held target. -/
theorem coordinatorAction_discover_current (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (r : RoundCoordinates p) (d : RoundPrivateValues x)
    (hm : st.mode = .discover)
    (ht : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = dataSlot)
    (a : Arm p.K) (ha : x.target = a) :
    BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t
        (ActiveRoundActions.coordinator p.two_le_m) = a := by
  rw [BootstrapPhysicalBlock.actions_coordinator,
    BootstrapPhysicalBlock.coordinatorAction_discover_data _ _ _ hm ht]
  simpa [currentInputOf, currentInput] using ha

/-- A positive physical coordinator observation in DISCOVER is exactly a
positive target reward together with avoidance by every other physical action.
This characterization retains collision feedback, including zero rewards and
already-true unoccupied-player cases. -/
theorem discover_feedback_pos_iff (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (r : RoundCoordinates p) (d : RoundPrivateValues x)
    (a : Arm p.K) (hm : st.mode = .discover)
    (ht : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = dataSlot)
    (htarget : x.target = a) :
    (0 < BootstrapPhysicalBlock.feedback (currentInputOf x t r d) st t
      (ActiveRoundActions.coordinator p.two_le_m)) ↔
      (chi x t a = 1 ∧
        FiniteBanditModel.collisionFreeFor
          (BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t)
          (ActiveRoundActions.coordinator p.two_le_m)) := by
  let y := currentInputOf x t r d
  have hcoord : BootstrapPhysicalBlock.actions y st t
      (ActiveRoundActions.coordinator p.two_le_m) = a := by
    exact coordinatorAction_discover_current x st t r d hm ht a htarget
  have hchi : 0 < (y.rewards t a).val ↔ chi x t a = 1 := by
    have hreward : y.rewards t a = x.rewards t a := by
      simp [y, currentInputOf, currentInput]
    rw [hreward]
    have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
    have hpos : 0 < (x.rewards t a).val ↔
        0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (x.rewards t a) := by
      rw [RealRewardGridCount.realRewardGridValue, div_pos_iff_of_pos_right hD]
      exact_mod_cast (Iff.rfl : 0 < (x.rewards t a).val ↔ 0 < (x.rewards t a).val)
    unfold chi
    rw [hpos]
    simp
  have hfeedback :
      (0 < BootstrapPhysicalBlock.feedback y st t
        (ActiveRoundActions.coordinator p.two_le_m)) ↔
      (chi x t a = 1 ∧
        FiniteBanditModel.collisionFreeFor (BootstrapPhysicalBlock.actions y st t)
          (ActiveRoundActions.coordinator p.two_le_m)) := by
    rw [← BootstrapPhysicalBlock.observationIndex_pos_iff]
    rw [BootstrapPhysicalBlock.observationIndex, hcoord]
    by_cases hfree : FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions y st t) (ActiveRoundActions.coordinator p.two_le_m)
    · simp [hfree, hchi]
    · simp [hfree]
  change (0 < BootstrapPhysicalBlock.feedback y st t
      (ActiveRoundActions.coordinator p.two_le_m)) ↔
    (chi x t a = 1 ∧
      FiniteBanditModel.collisionFreeFor (BootstrapPhysicalBlock.actions y st t)
        (ActiveRoundActions.coordinator p.two_le_m))
  exact hfeedback

/-- In the DISCOVER snapshot, the indicator event is exactly the source
rounded-reward support together with collision freedom of the actual profile. -/
theorem discoveryIndicator_eq_one_iff (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (r : RoundCoordinates p) (d : RoundPrivateValues x)
    (_hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (a : Arm p.K) (hm : st.mode = .discover)
    (ht : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = dataSlot)
    (htarget : x.target = a) :
    discoveryIndicator x st t r d = 1 ↔
      chi x t a = 1 ∧ FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t)
        (ActiveRoundActions.coordinator p.two_le_m) := by
  simp [discoveryIndicator, hm, ht,
    discover_feedback_pos_iff x st t r d a hm ht htarget]

/-- On DATA MULTICAST the coordinator action is still the existing physical
release rule, with the entire list product evaluated at the current snapshot. -/
theorem multicastCoordinatorAction_current (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (r : RoundCoordinates p) (d : RoundPrivateValues x)
    (_hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (hm : st.mode = .multicast)
    (ht : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = dataSlot) :
    BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t
        (ActiveRoundActions.coordinator p.two_le_m) =
      if BootstrapPhysicalBlock.forwardProduct (currentInputOf x t r d) st t = 1 then
        (currentInputOf x t r d).coordinatorAvoid t |>.val
      else (currentInputOf x t r d).target := by
  rw [BootstrapPhysicalBlock.actions_coordinator,
    BootstrapPhysicalBlock.coordinatorAction_multicast_data _ _ _ hm ht]

/-- Under the fixed isolation premise, an ID-zero distinguished follower uses
its held arm in the actual physical action profile. -/
theorem distinguishedFollower_IDzero_action (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (r : RoundCoordinates p) (d : RoundPrivateValues x)
    (hactive : x.active j = true)
    (hid : x.ids (x.privateId j) t = false) :
    BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t
      (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) = x.held j := by
  let y := currentInputOf x t r d
  have hmem : j.val ∈ y.uninformed := by simp [y, currentInputOf, currentInput]
  let jy : {k // k ∈ y.uninformed} := ⟨j.val, hmem⟩
  have hactiveY : y.active jy = true := by simp [jy, y, currentInputOf, currentInput, hactive]
  have hidY : y.ids (y.privateId jy) t = false := by
    simpa [jy, y, currentInputOf, currentInput] using hid
  calc
    BootstrapPhysicalBlock.actions y st t (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) =
        BootstrapPhysicalBlock.uninformedAction y t jy := by
          simp [BootstrapPhysicalBlock.actions_follower, BootstrapPhysicalBlock.followerAction,
            jy, hmem]
    _ = y.held jy := BootstrapPhysicalBlock.uninformedAction_stay y t jy hactiveY hidY
    _ = x.held j := by simp [jy, y, currentInputOf, currentInput]

/-- Under the same isolation premise, ID one selects the actual genuine
held-arm complement draw and therefore avoids the held arm. -/
theorem distinguishedFollower_IDone_avoids_held (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (r : RoundCoordinates p) (d : RoundPrivateValues x)
    (hactive : x.active j = true)
    (hid : x.ids (x.privateId j) t = true) :
    BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t
      (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) ≠ x.held j := by
  let y := currentInputOf x t r d
  have hmem : j.val ∈ y.uninformed := by simp [y, currentInputOf, currentInput]
  let jy : {k // k ∈ y.uninformed} := ⟨j.val, hmem⟩
  have hactiveY : y.active jy = true := by simp [jy, y, currentInputOf, currentInput, hactive]
  have hidY : y.ids (y.privateId jy) t = true := by
    simpa [jy, y, currentInputOf, currentInput] using hid
  calc
    BootstrapPhysicalBlock.actions y st t (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) =
        BootstrapPhysicalBlock.uninformedAction y t jy := by
          simp [BootstrapPhysicalBlock.actions_follower, BootstrapPhysicalBlock.followerAction,
            jy, hmem]
    _ ≠ y.held jy := BootstrapPhysicalBlock.uninformedAction_avoid y t jy hactiveY hidY
    _ = x.held j := by simp [jy, y, currentInputOf, currentInput]

/-- With the stipulated held target and ID-zero bit, MULTICAST's follower
indicator is exactly positive target support and collision freedom in the
actual physical profile.  List membership, list cutoff, and calendar location
remain explicit hypotheses of this source-facing service case. -/
theorem multicastIndicator_eq_one_iff (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (r : RoundCoordinates p) (d : RoundPrivateValues x)
    (_hcal : t ∈ BootstrapDimensions.calendarBlock p s)
    (_hmem : x.privateId j ∈ st.list) (_hcard : st.list.card ≤ L0 p)
    (a : Arm p.K) (hm : st.mode = .multicast)
    (ht : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = dataSlot)
    (hactive : x.active j = true)
    (hid : x.ids (x.privateId j) t = false)
    (hheld : x.held j = a) (_htarget : x.target = a) :
    multicastIndicator x st t j r d = 1 ↔
      chi x t a = 1 ∧ FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t)
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) := by
  let y := currentInputOf x t r d
  have hact : BootstrapPhysicalBlock.actions y st t
      (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) = a := by
    have hmem : j.val ∈ y.uninformed := by simp [y, currentInputOf, currentInput]
    let jy : {k // k ∈ y.uninformed} := ⟨j.val, hmem⟩
    have hactiveY : y.active jy = true := by
      simp [jy, y, currentInputOf, currentInput, hactive]
    have hidY : y.ids (y.privateId jy) t = false := by
      simpa [jy, y, currentInputOf, currentInput] using hid
    calc
      BootstrapPhysicalBlock.actions y st t
          (PublicDiscreteDraws.followerPlayer p.two_le_m j.val) =
          BootstrapPhysicalBlock.uninformedAction y t jy := by
            simp [BootstrapPhysicalBlock.actions_follower,
              BootstrapPhysicalBlock.followerAction, jy, hmem]
      _ = y.held jy := BootstrapPhysicalBlock.uninformedAction_stay y t jy hactiveY hidY
      _ = a := by simpa [jy, y, currentInputOf, currentInput] using hheld
  have hchi : 0 < (y.rewards t a).val ↔ chi x t a = 1 := by
    have hreward : y.rewards t a = x.rewards t a := by
      simp [y, currentInputOf, currentInput]
    rw [hreward]
    have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
    have hpos : 0 < (x.rewards t a).val ↔
        0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (x.rewards t a) := by
      rw [RealRewardGridCount.realRewardGridValue, div_pos_iff_of_pos_right hD]
      exact_mod_cast (Iff.rfl : 0 < (x.rewards t a).val ↔ 0 < (x.rewards t a).val)
    unfold chi
    rw [hpos]
    simp
  have hfeedback :
      (0 < BootstrapPhysicalBlock.feedback y st t
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.val)) ↔
      (chi x t a = 1 ∧ FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions y st t)
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.val)) := by
    rw [← BootstrapPhysicalBlock.observationIndex_pos_iff,
      BootstrapPhysicalBlock.observationIndex, hact]
    by_cases hfree : FiniteBanditModel.collisionFreeFor
        (BootstrapPhysicalBlock.actions y st t)
        (PublicDiscreteDraws.followerPlayer p.two_le_m j.val)
    · simp [hfree, hchi]
    · simp [hfree]
  change multicastIndicator x st t j r d = 1 ↔
    chi x t a = 1 ∧ FiniteBanditModel.collisionFreeFor
      (BootstrapPhysicalBlock.actions y st t)
      (PublicDiscreteDraws.followerPlayer p.two_le_m j.val)
  simp [multicastIndicator, hm, ht, hid, hfeedback, y]

/-- When the coordinator has its private ID in the multicast list, the
empty-list branch is unavailable by membership itself. -/
theorem multicast_membership_nonempty (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p)
    (j : {j // j ∈ x.uninformed})
    (hmem : x.privateId j ∈ st.list) : st.list.Nonempty :=
  ⟨x.privateId j, hmem⟩

/-- The existing isolation lemma supplies the elementary avoidance power
bound, with the actual accepted dimensions and no altered exponent. -/
theorem otherPlayerAvoidance_power (p : ConstructorDimensions.Parameters) :
    (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) ≥ 1 / 4 := by
  have hsource := BootstrapBlockIsolation.inactivity_power_lower_bound p
  have hmpos : (0 : ℝ) < (p.m : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
  have hmK : (p.m : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast Nat.le_of_lt p.m_lt_K
  have hrecip : 1 / (p.K : ℝ) ≤ 1 / (p.m : ℝ) :=
    one_div_le_one_div_of_le hmpos hmK
  have hbase : 1 - 1 / (p.m : ℝ) ≤ 1 - 1 / (p.K : ℝ) := by linarith
  have hmone : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
  have hrecip_le_one : 1 / (p.m : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hmone
  have hbase_nonneg : 0 ≤ 1 - 1 / (p.m : ℝ) := by linarith
  have hpower := pow_le_pow_left₀ hbase_nonneg hbase (p.m - 2)
  exact hsource.trans hpower

end Bandits.Support.BootstrapModeService

end
