/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapIntervalBounds
public import Bandits.Support.BootstrapPrivateRoundStreams
public import Bandits.Support.BootstrapPhysicalInput
public import Bandits.Support.GeneratedBootstrapRoundLaw
public import Bandits.Support.PrivateSourceStreams

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Simultaneous tail for original latent activity coins

The event here uses the first, original private scalar for each follower and
calendar block, continued through the full bootstrap horizon.  The probability
proof is performed on the accepted product of labelled scalar profiles and
then lifted through the original row/private product.

Source: `sources/zip4/manuscript/appendix_b_communication.tex:598-621` and
`sources/zip4/manuscript/07_public_setup.tex:27-38,63-73`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal

namespace Bandits.Support.GeneratedLatentActivityTail

open ConstructorDimensions BootstrapDimensions PrivateSourceStreams
open BootstrapPrivateRoundStreams GeneratedBootstrapRoundLaw
open BootstrapPhysicalInput BootstrapIntervalBounds
open BootstrapBlockConstruction
open PublicDiscreteDraws CompletePublicTable FiniteBanditModel

/-- The real indicator of a Boolean event. -/
noncomputable def coinToReal (b : Bool) : ℝ :=
  ({true} : Set Bool).indicator (fun _ => 1) b

theorem measurable_coinToReal : Measurable coinToReal :=
  measurable_const.indicator (measurableSet_singleton true)

theorem coinToReal_unit_bounds (b : Bool) : 0 ≤ coinToReal b ∧ coinToReal b ≤ 1 := by
  cases b <;> simp [coinToReal]

/-- Activity decoded from the first original scalar in one follower/block
profile.  The held-arm and private-ID scalars are not used. -/
noncomputable def profileActivityCoin (p : Parameters) (j : Fin (p.m - 1))
    (profile : Fin (p.m - 1) → BlockScalars) : Bool :=
  activityScalarDraw p ((profile j).1)

/-- The real indicator carried by a labelled follower/block profile. -/
noncomputable def profileActivityValue (p : Parameters) (j : Fin (p.m - 1))
    (profile : Fin (p.m - 1) → BlockScalars) : ℝ :=
  coinToReal (profileActivityCoin p j profile)

theorem measurable_profileActivityCoin (p : Parameters) (j : Fin (p.m - 1)) :
    Measurable (profileActivityCoin p j) := by
  exact (activityScalarDraw_measurable p).comp
    (measurable_fst.comp (measurable_pi_apply j))

theorem measurable_profileActivityValue (p : Parameters) (j : Fin (p.m - 1)) :
    Measurable (profileActivityValue p j) :=
  measurable_coinToReal.comp (measurable_profileActivityCoin p j)

/-- The first scalar coordinate of one accepted follower/block triple has the
original uniform law, so its threshold coin has the prescribed Bernoulli law. -/
noncomputable def activityCoinLaw (p : Parameters) : Measure Bool :=
  ContinuousCategorical.uniform.map (activityScalarDraw p)

theorem activityCoinLaw_true_mass (p : Parameters) :
    activityCoinLaw p {true} = ENNReal.ofReal (1 / (p.m : ℝ)) := by
  rw [activityCoinLaw,
    Measure.map_apply (activityScalarDraw_measurable p) (measurableSet_singleton true)]
  simpa [BootstrapBlockConstruction.activityProbability] using
    activityScalarDraw_uniform_mass p true

theorem profileActivityCoin_law (p : Parameters) (j : Fin (p.m - 1)) :
    (blockScalarProfileLaw p).map (profileActivityCoin p j) = activityCoinLaw p := by
  let firstCoin : BlockScalars → Bool := fun x => activityScalarDraw p x.1
  have hfirstCoin : Measurable firstCoin :=
    (activityScalarDraw_measurable p).comp measurable_fst
  have hfirst : blockScalarsLaw.map Prod.fst = ContinuousCategorical.uniform := by
    simp [blockScalarsLaw]
  have htriple : blockScalarsLaw.map firstCoin = activityCoinLaw p := by
    change blockScalarsLaw.map (activityScalarDraw p ∘ Prod.fst) = _
    exact (Measure.map_map (activityScalarDraw_measurable p) measurable_fst).symm.trans
      (congrArg (fun μ => μ.map (activityScalarDraw p)) hfirst)
  have heval : (blockScalarProfileLaw p).map (fun x => x j) = blockScalarsLaw := by
    change (Measure.pi (fun _ : Fin (p.m - 1) => blockScalarsLaw)).map
      (fun x => x j) = blockScalarsLaw
    simpa using
      (measurePreserving_eval (fun _ : Fin (p.m - 1) => blockScalarsLaw) j).map_eq
  calc
    (blockScalarProfileLaw p).map (profileActivityCoin p j) =
        ((blockScalarProfileLaw p).map (fun x => x j)).map firstCoin := by
          exact (Measure.map_map hfirstCoin (measurable_pi_apply j)).symm
    _ = activityCoinLaw p := by rw [heval, htriple]

theorem profileActivityValue_integral (p : Parameters) (j : Fin (p.m - 1)) :
    ∫ profile, profileActivityValue p j profile ∂blockScalarProfileLaw p =
      1 / (p.m : ℝ) := by
  calc
    ∫ profile, profileActivityValue p j profile ∂blockScalarProfileLaw p =
        ∫ b, coinToReal b ∂(blockScalarProfileLaw p).map (profileActivityCoin p j) := by
          exact (integral_map
            (measurable_profileActivityCoin p j).aemeasurable
            measurable_coinToReal.aestronglyMeasurable).symm
    _ = ∫ b, coinToReal b ∂activityCoinLaw p := by
          rw [profileActivityCoin_law]
    _ = (activityCoinLaw p {true}).toReal := by
          change ∫ b, ({true} : Set Bool).indicator (fun _ => (1 : ℝ)) b
              ∂activityCoinLaw p = _
          rw [integral_indicator_const 1 (measurableSet_singleton true)]
          simp [Measure.real]
    _ = 1 / (p.m : ℝ) := by
          rw [activityCoinLaw_true_mass, ENNReal.toReal_ofReal]
          exact div_nonneg (by norm_num) (Nat.cast_nonneg _)

/-- The exact labelled source follower/block inputs on which the clock is
proved. -/
abbrev RawFollowerBlocks (p : Parameters) := FollowerBlockInputs p

/-- One original activity coin, as a real zero/one value, on the accepted raw
follower/block product. -/
noncomputable def rawActivityValue (p : Parameters) (j : Fin (p.m - 1))
    (s : Fin (n_boot p)) (x : RawFollowerBlocks p) : ℝ :=
  profileActivityValue p j (x s)

/-- The original activity coin stream across every calendar block. -/
noncomputable def rawActivityCoinStream (p : Parameters) (j : Fin (p.m - 1))
    (x : RawFollowerBlocks p) : Fin (n_boot p) → Bool :=
  fun s => profileActivityCoin p j (x s)

theorem measurable_rawActivityCoinStream (p : Parameters) (j : Fin (p.m - 1)) :
    Measurable (rawActivityCoinStream p j) := by
  apply measurable_pi_iff.mpr
  intro s
  exact measurable_profileActivityCoin p j |>.comp (measurable_pi_apply s)

/-- The labelled raw coin stream has the finite product of the original
Bernoulli laws, with each block marginal induced by its original first scalar. -/
theorem rawActivityCoinStream_product_law (p : Parameters) (j : Fin (p.m - 1)) :
    (followerBlockInputsLaw p).map (rawActivityCoinStream p j) =
      Measure.pi (fun _ : Fin (n_boot p) => activityCoinLaw p) := by
  have hblocks : ProbabilityTheory.iIndepFun
      (fun q : Fin (n_boot p) => fun x : RawFollowerBlocks p => x q)
      (followerBlockInputsLaw p) := by
    change ProbabilityTheory.iIndepFun
      (fun q : Fin (n_boot p) => fun x : Fin (n_boot p) →
        Fin (p.m - 1) → BlockScalars => x q)
      (Measure.pi (fun _ : Fin (n_boot p) => blockScalarProfileLaw p))
    exact ProbabilityTheory.iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hcoins := hblocks.comp
    (fun _ : Fin (n_boot p) => profileActivityCoin p j)
    (fun _ => measurable_profileActivityCoin p j)
  have hmeas : ∀ s : Fin (n_boot p),
      AEMeasurable (fun x : RawFollowerBlocks p => profileActivityCoin p j (x s))
        (followerBlockInputsLaw p) := by
    intro s
    exact (measurable_profileActivityCoin p j).comp
      (measurable_pi_apply s) |>.aemeasurable
  have hproduct := hcoins.map_fun_eq_pi_map hmeas
  calc
    (followerBlockInputsLaw p).map (rawActivityCoinStream p j) =
        (followerBlockInputsLaw p).map
          (fun x s => profileActivityCoin p j (x s)) := by rfl
    _ = Measure.pi (fun _ : Fin (n_boot p) => activityCoinLaw p) := by
      rw [hproduct]
      congr 1
      funext s
      have heval : (followerBlockInputsLaw p).map (fun x => x s) =
          blockScalarProfileLaw p := by
        change (Measure.pi (fun _ : Fin (n_boot p) => blockScalarProfileLaw p)).map
          (fun x => x s) = blockScalarProfileLaw p
        simpa using
          (measurePreserving_eval (fun _ : Fin (n_boot p) => blockScalarProfileLaw p) s).map_eq
      calc
        (followerBlockInputsLaw p).map
            (fun x => profileActivityCoin p j (x s)) =
            ((followerBlockInputsLaw p).map (fun x => x s)).map
              (profileActivityCoin p j) := by
                exact (Measure.map_map (measurable_profileActivityCoin p j)
                  (measurable_pi_apply s)).symm
        _ = activityCoinLaw p := by rw [heval, profileActivityCoin_law]

theorem measurable_rawActivityValue (p : Parameters) (j : Fin (p.m - 1))
    (s : Fin (n_boot p)) : Measurable (rawActivityValue p j s) :=
  (measurable_profileActivityValue p j).comp (measurable_pi_apply s)

theorem rawActivityValue_unit_bounds (p : Parameters) (j : Fin (p.m - 1))
    (s : Fin (n_boot p)) (x : RawFollowerBlocks p) :
    0 ≤ rawActivityValue p j s x ∧ rawActivityValue p j s x ≤ 1 := by
  exact coinToReal_unit_bounds _

/-- Literal finite prefix count, summing the original coin at each source
block label `s.val < r`. -/
noncomputable def rawActivityPrefixCount (p : Parameters) (j : Fin (p.m - 1))
    (r : ℕ) (x : RawFollowerBlocks p) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s : Fin (n_boot p) => s.val < r),
    rawActivityValue p j s x

theorem measurable_rawActivityPrefixCount (p : Parameters) (j : Fin (p.m - 1))
    (r : ℕ) : Measurable (rawActivityPrefixCount p j r) := by
  classical
  unfold rawActivityPrefixCount
  exact (Finset.univ.filter (fun s : Fin (n_boot p) => s.val < r)).measurable_fun_sum
    (fun s _ => measurable_rawActivityValue p j s)

/-- Tail event for the literal original scalar coins on the raw product. -/
def rawActivityTailEvent (p : Parameters) (j : Fin (p.m - 1)) :
    Set (RawFollowerBlocks p) :=
  ⋃ r : {r : ℕ // r ≤ n_boot p},
    {x | 2 * (r.1 : ℝ) / (p.m : ℝ) + 4 * (b_N p : ℝ) <
      rawActivityPrefixCount p j r.1 x}

theorem measurable_rawActivityTailEvent (p : Parameters) (j : Fin (p.m - 1)) :
    MeasurableSet (rawActivityTailEvent p j) := by
  apply MeasurableSet.iUnion
  intro r
  exact measurableSet_lt measurable_const (measurable_rawActivityPrefixCount p j r.1)

/-- Proof-local filtration generated by strict prefixes of the original raw
block profiles. -/
@[instance_reducible] def rawBlockPrefixSigma (p : Parameters) (r : ℕ) :
    MeasurableSpace (RawFollowerBlocks p) :=
  ⨆ s : Fin (n_boot p), ⨆ (_h : s.val < r),
    MeasurableSpace.comap (fun x : RawFollowerBlocks p => x s) inferInstance

def rawBlockPrefixFiltration (p : Parameters) :
    Filtration ℕ (inferInstance : MeasurableSpace (RawFollowerBlocks p)) where
  seq := rawBlockPrefixSigma p
  mono' := by
    intro r q hrq
    apply iSup₂_le
    intro s hs
    apply le_iSup_of_le s
    apply le_iSup_of_le (lt_of_lt_of_le hs hrq)
    exact le_rfl
  le' := by
    intro r
    apply iSup₂_le
    intro s hs
    exact (measurable_pi_apply s).comap_le

/-- The one-indexed clock variable used by the accepted interval bound; at
time `t` it is the source block `s=t-1`. Outside the proved horizon it is
zero, which is immaterial to the source event. -/
noncomputable def activityClockValue (p : Parameters) (j : Fin (p.m - 1))
    (t : ℕ) (x : RawFollowerBlocks p) : ℝ :=
  if ht : 0 < t ∧ t ≤ n_boot p then
    rawActivityValue p j ⟨t - 1, by omega⟩ x
  else 0

private theorem activityClockValue_eq_raw (p : Parameters) (j : Fin (p.m - 1))
    (t : ℕ) (ht₁ : 1 ≤ t) (ht₂ : t ≤ n_boot p) :
    activityClockValue p j t = rawActivityValue p j ⟨t - 1, by omega⟩ := by
  have hvalid : 0 < t ∧ t ≤ n_boot p := ⟨by omega, ht₂⟩
  funext x
  simp [activityClockValue, hvalid]

theorem activityClockValue_measurable (p : Parameters) (j : Fin (p.m - 1))
    (t : ℕ) (ht₁ : 1 ≤ t) (ht₂ : t ≤ n_boot p) :
    Measurable[rawBlockPrefixFiltration p t] (activityClockValue p j t) := by
  have hlabel : t - 1 < t := by omega
  have hcoord :
      MeasurableSpace.comap (fun x : RawFollowerBlocks p =>
        x (⟨t - 1, by omega⟩ : Fin (n_boot p))) inferInstance ≤
          rawBlockPrefixFiltration p t := by
    apply le_iSup_of_le ⟨t - 1, by omega⟩
    apply le_iSup_of_le hlabel
    exact le_rfl
  have hcoin : Measurable[
      MeasurableSpace.comap (fun x : RawFollowerBlocks p =>
        x (⟨t - 1, by omega⟩ : Fin (n_boot p))) inferInstance]
      (activityClockValue p j t) := by
    rw [activityClockValue_eq_raw p j t ht₁ ht₂]
    exact (measurable_profileActivityValue p j).comp
      (comap_measurable _)
  exact hcoin.mono hcoord le_rfl

theorem activityClockValue_unit_bounds (p : Parameters) (j : Fin (p.m - 1))
    (t : ℕ) (ht₁ : 1 ≤ t) (ht₂ : t ≤ n_boot p)
    (x : RawFollowerBlocks p) :
    0 ≤ activityClockValue p j t x ∧ activityClockValue p j t x ≤ 1 := by
  rw [activityClockValue_eq_raw p j t ht₁ ht₂]
  exact rawActivityValue_unit_bounds p j ⟨t - 1, by omega⟩ x

theorem rawActivityValue_integral (p : Parameters) (j : Fin (p.m - 1))
    (s : Fin (n_boot p)) :
    ∫ x, rawActivityValue p j s x ∂followerBlockInputsLaw p = 1 / (p.m : ℝ) := by
  have heval : (followerBlockInputsLaw p).map (fun x => x s) = blockScalarProfileLaw p := by
    change (Measure.pi (fun _ : Fin (n_boot p) => blockScalarProfileLaw p)).map
      (fun x => x s) = blockScalarProfileLaw p
    simpa using
      (measurePreserving_eval (fun _ : Fin (n_boot p) => blockScalarProfileLaw p) s).map_eq
  calc
    ∫ x, rawActivityValue p j s x ∂followerBlockInputsLaw p =
        ∫ profile, profileActivityValue p j profile ∂
          (followerBlockInputsLaw p).map (fun x => x s) := by
            exact (integral_map (measurable_pi_apply s).aemeasurable
              (measurable_profileActivityValue p j).aestronglyMeasurable).symm
    _ = 1 / (p.m : ℝ) := by rw [heval, profileActivityValue_integral]

theorem activityClockValue_integral (p : Parameters) (j : Fin (p.m - 1))
    (t : ℕ) (ht₁ : 1 ≤ t) (ht₂ : t ≤ n_boot p) :
    ∫ x, activityClockValue p j t x ∂followerBlockInputsLaw p = 1 / (p.m : ℝ) := by
  rw [activityClockValue_eq_raw p j t ht₁ ht₂]
  exact rawActivityValue_integral p j ⟨t - 1, by omega⟩

theorem rawActivityClock_conditionalMean (p : Parameters) (j : Fin (p.m - 1))
    (t : ℕ) (ht₁ : 1 ≤ t) (ht₂ : t ≤ n_boot p) :
    (followerBlockInputsLaw p)[activityClockValue p j t |
      rawBlockPrefixFiltration p (t - 1)] =ᵐ[followerBlockInputsLaw p]
        fun _ => 1 / (p.m : ℝ) := by
  let s : Fin (n_boot p) := ⟨t - 1, by omega⟩
  have hblocks : ProbabilityTheory.iIndepFun
      (fun q : Fin (n_boot p) => fun x : RawFollowerBlocks p => x q)
      (followerBlockInputsLaw p) := by
    change ProbabilityTheory.iIndepFun
      (fun q : Fin (n_boot p) => fun x : Fin (n_boot p) →
        Fin (p.m - 1) → BlockScalars => x q)
      (Measure.pi (fun _ : Fin (n_boot p) => blockScalarProfileLaw p))
    exact ProbabilityTheory.iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hcoordIndep : Indep
      (MeasurableSpace.comap (fun x : RawFollowerBlocks p => x s) inferInstance)
      (rawBlockPrefixSigma p s.val) (followerBlockInputsLaw p) := by
    have hdisj : Disjoint ({s} : Set (Fin (n_boot p)))
        {q : Fin (n_boot p) | q.val < s.val} := by
      apply Set.disjoint_left.mpr
      intro q hsingle hprefix
      have hqs : q = s := Set.mem_singleton_iff.mp hsingle
      subst q
      exact (Nat.lt_irrefl _ hprefix).elim
    have hind := indep_iSup_of_disjoint
      (fun q => (measurable_pi_apply q).comap_le) hblocks.iIndep hdisj
    simpa [rawBlockPrefixSigma] using hind
  have hmeas : StronglyMeasurable[
      MeasurableSpace.comap (fun x : RawFollowerBlocks p => x s) inferInstance]
      (activityClockValue p j t) := by
    rw [activityClockValue_eq_raw p j t ht₁ ht₂]
    exact ((measurable_profileActivityValue p j).comp
      (comap_measurable _)).stronglyMeasurable
  have hprefixLe : rawBlockPrefixSigma p s.val ≤
      (inferInstance : MeasurableSpace (RawFollowerBlocks p)) :=
    (rawBlockPrefixFiltration p).le s.val
  have hcond := condExp_indep_eq
    ((measurable_pi_apply s).comap_le) hprefixLe
    hmeas hcoordIndep
  have hint : ∫ x, activityClockValue p j t x ∂followerBlockInputsLaw p =
      1 / (p.m : ℝ) := activityClockValue_integral p j t ht₁ ht₂
  filter_upwards [hcond] with x hx
  simpa [BootstrapIntervalBounds.conditionalMean, rawBlockPrefixFiltration, s, hint] using hx

private theorem rawPrefixCount_eq_intervalSum (p : Parameters)
    (j : Fin (p.m - 1)) (r : ℕ) (hr : r ≤ n_boot p)
    (x : RawFollowerBlocks p) :
    rawActivityPrefixCount p j r x =
      BootstrapIntervalBounds.intervalSum (activityClockValue p j) 1
        (n_boot p) r x := by
  classical
  rw [BootstrapIntervalBounds.intervalSum_eq_sum_Icc (activityClockValue p j) hr x]
  apply Finset.sum_bij (fun s _ => s.val + 1)
  · intro s hs
    have hslt : s.val < r := (Finset.mem_filter.mp hs).2
    simp only [Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  · intro s₁ hs₁ s₂ hs₂ heq
    apply Fin.ext
    exact Nat.add_right_cancel heq
  · intro t ht
    rcases Finset.mem_Icc.mp ht with ⟨ht₁, htr⟩
    have htn : t ≤ n_boot p := htr.trans hr
    have hlabel : t - 1 < n_boot p := by omega
    refine ⟨⟨t - 1, hlabel⟩, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by
        change t - 1 < r
        omega⟩
    · change (t - 1) + 1 = t
      omega
  · intro s hs
    have hslt : s.val < r := (Finset.mem_filter.mp hs).2
    have ht₁ : 0 < s.val + 1 := by omega
    have ht₂ : s.val + 1 ≤ n_boot p := by omega
    have hlabel : (⟨s.val + 1 - 1, by omega⟩ : Fin (n_boot p)) = s := by
      apply Fin.ext
      simp
    rw [activityClockValue_eq_raw p j (s.val + 1) (by omega) ht₂]
    rw [hlabel]

private theorem rawActivityTail_subset_intervalFailure_ae (p : Parameters)
    (j : Fin (p.m - 1)) :
    rawActivityTailEvent p j ≤ᵐ[followerBlockInputsLaw p]
      (BootstrapIntervalBounds.upperGood (followerBlockInputsLaw p)
        (rawBlockPrefixFiltration p) (activityClockValue p j) 1
        (n_boot p) (4 * (b_N p : ℝ)))ᶜ := by
  have hmeans : ∀ᵐ x ∂followerBlockInputsLaw p,
      ∀ t ∈ Set.Icc 1 (n_boot p),
        BootstrapIntervalBounds.conditionalMean (followerBlockInputsLaw p)
          (rawBlockPrefixFiltration p) (activityClockValue p j) t x =
            1 / (p.m : ℝ) := by
    apply ae_all_iff.mpr
    intro t
    by_cases ht : t ∈ Set.Icc 1 (n_boot p)
    · rcases Set.mem_Icc.mp ht with ⟨ht₁, ht₂⟩
      filter_upwards [rawActivityClock_conditionalMean p j t ht₁ ht₂] with x hx
      exact fun _ => hx
    · exact ae_of_all _ fun _ ht' => (ht ht').elim
  filter_upwards [hmeans] with x hmean
  intro hx
  rcases Set.mem_iUnion.mp hx with ⟨r, hbad⟩
  have hr : r.1 ≤ n_boot p := r.2
  change 2 * (r.1 : ℝ) / (p.m : ℝ) + 4 * (b_N p : ℝ) <
    rawActivityPrefixCount p j r.1 x at hbad
  by_cases hr0 : r.1 = 0
  · have hcount : rawActivityPrefixCount p j r.1 x = 0 := by
      unfold rawActivityPrefixCount
      have hempty : Finset.univ.filter
          (fun s : Fin (n_boot p) => s.val < r.1) = ∅ := by
        ext s
        simp [hr0]
      rw [hempty, Finset.sum_empty]
    have hbad0 : 4 * (b_N p : ℝ) < rawActivityPrefixCount p j r.1 x := by
      simpa [hr0] using hbad
    have : 4 * (b_N p : ℝ) < 0 := by
      rw [hcount] at hbad0
      exact hbad0
    have hnonneg : 0 ≤ 4 * (b_N p : ℝ) := by positivity
    linarith
  · have hrpos : 1 ≤ r.1 := by omega
    have hrIcc : r.1 ∈ Set.Icc 1 (n_boot p) := ⟨hrpos, hr⟩
    have hsum := rawPrefixCount_eq_intervalSum p j r.1 hr x
    have hmeanSum :
        (∑ t ∈ Finset.Icc 1 r.1,
          BootstrapIntervalBounds.conditionalMean (followerBlockInputsLaw p)
            (rawBlockPrefixFiltration p) (activityClockValue p j) t x) =
          (r.1 : ℝ) / (p.m : ℝ) := by
      calc
        _ = ∑ _t ∈ Finset.Icc 1 r.1, (1 / (p.m : ℝ)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hmean t ⟨(Finset.mem_Icc.mp ht).1,
            (Finset.mem_Icc.mp ht).2.trans hr⟩]
        _ = (r.1 : ℝ) / (p.m : ℝ) := by
          simp [Finset.sum_const, Nat.card_Icc]
          ring
    have hnotgood : x ∉ BootstrapIntervalBounds.upperGood
        (followerBlockInputsLaw p) (rawBlockPrefixFiltration p)
        (activityClockValue p j) 1 (n_boot p) (4 * (b_N p : ℝ)) := by
      intro hg
      have hclock := hg r.1 hrIcc
      rw [← hsum,
        BootstrapIntervalBounds.intervalSum_eq_sum_Icc
          (BootstrapIntervalBounds.conditionalMean (followerBlockInputsLaw p)
            (rawBlockPrefixFiltration p) (activityClockValue p j)) hr x,
        hmeanSum] at hclock
      have hscale : 2 * ((r.1 : ℝ) / (p.m : ℝ)) =
          2 * (r.1 : ℝ) / (p.m : ℝ) := by ring
      rw [← hscale] at hbad
      exact (not_le_of_gt hbad) hclock
    exact hnotgood

theorem rawActivity_prefix_tail (p : Parameters) (j : Fin (p.m - 1)) :
    (followerBlockInputsLaw p).real (rawActivityTailEvent p j) ≤
      Real.exp (-(4 * (b_N p : ℝ))) := by
  have hX : ∀ t, 1 ≤ t → t ≤ n_boot p →
      StronglyMeasurable[rawBlockPrefixFiltration p t] (activityClockValue p j t) :=
    fun t ht₁ ht₂ => (activityClockValue_measurable p j t ht₁ ht₂).stronglyMeasurable
  have hb : ∀ t, 1 ≤ t → t ≤ n_boot p →
      ∀ᵐ x ∂followerBlockInputsLaw p,
        0 ≤ activityClockValue p j t x ∧ activityClockValue p j t x ≤ 1 := by
    intro t ht₁ ht₂
    exact ae_of_all _ (activityClockValue_unit_bounds p j t ht₁ ht₂)
  have hα : 1 ≤ 1 := le_rfl
  have hαT : 1 ≤ n_boot p := by
    exact Nat.succ_le_of_lt (BootstrapDimensions.n_boot_pos p)
  have hclock := BootstrapIntervalBounds.upper_failure_localized
    (P := followerBlockInputsLaw p) (F := rawBlockPrefixFiltration p)
    (X := activityClockValue p j) (α := 1) (T := n_boot p)
    hX hb hα hαT (4 * (b_N p : ℝ))
    (A := Set.univ) MeasurableSet.univ
  have hfailure : (followerBlockInputsLaw p).real
      ((BootstrapIntervalBounds.upperGood (followerBlockInputsLaw p)
        (rawBlockPrefixFiltration p) (activityClockValue p j) 1
        (n_boot p) (4 * (b_N p : ℝ)))ᶜ) ≤ Real.exp (-(4 * (b_N p : ℝ))) := by
    simpa using hclock
  have hsubset := rawActivityTail_subset_intervalFailure_ae p j
  have hmeasure : (followerBlockInputsLaw p) (rawActivityTailEvent p j) ≤
      (followerBlockInputsLaw p)
        ((BootstrapIntervalBounds.upperGood (followerBlockInputsLaw p)
          (rawBlockPrefixFiltration p) (activityClockValue p j) 1
          (n_boot p) (4 * (b_N p : ℝ)))ᶜ) :=
    measure_mono_ae hsubset
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hmeasure).trans hfailure

/-- The requested literal original coin on a genuine original round-law point.
It is the very same first scalar used by the physical profile map. -/
noncomputable def originalActivityCoin (p : Parameters) (i : ActiveRoundActions.Follower p.m)
    (s : Fin (n_boot p)) (e : Coordinates p) : Bool :=
  PrivateSourceStreams.activityScalarDraw p
    (((e.2.1.1 s) (BootstrapPhysicalInput.sourceFollowerIndex p i)).1)

/-- The manuscript's simultaneous original-coin prefix count, with source
labels `s.val < r` and both endpoints included in the event below. -/
noncomputable def originalActivityPrefixCount (p : Parameters)
    (i : ActiveRoundActions.Follower p.m)
    (r : ℕ) (e : Coordinates p) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s : Fin (n_boot p) => s.val < r),
    coinToReal (originalActivityCoin p i s e)

noncomputable def originalActivityTailEvent (p : Parameters)
    (i : ActiveRoundActions.Follower p.m) :
    Set (Coordinates p) :=
  {e | ∃ r : {r : ℕ // r ≤ n_boot p},
    2 * (r.1 : ℝ) / (p.m : ℝ) + 4 * (b_N p : ℝ) <
      originalActivityPrefixCount p i r.1 e}

noncomputable def extendedActivityPrefixCount (p : Parameters)
    (i : ActiveRoundActions.Follower p.m)
    (r : ℕ) (x : ExtendedPrivateCoordinates p) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s : Fin (n_boot p) => s.val < r),
    coinToReal (activityScalarDraw p
      (((x.1.1 s) (BootstrapPhysicalInput.sourceFollowerIndex p i)).1))

noncomputable def extendedActivityTailEvent (p : Parameters)
    (i : ActiveRoundActions.Follower p.m) :
    Set (ExtendedPrivateCoordinates p) :=
  {x | ∃ r : {r : ℕ // r ≤ n_boot p},
    2 * (r.1 : ℝ) / (p.m : ℝ) + 4 * (b_N p : ℝ) <
      extendedActivityPrefixCount p i r.1 x}

theorem originalActivityTailEvent_eq_raw_preimage (p : Parameters)
    (i : ActiveRoundActions.Follower p.m) :
    originalActivityTailEvent p i =
      (fun e : Coordinates p => e.2.1.1) ⁻¹'
        rawActivityTailEvent p (BootstrapPhysicalInput.sourceFollowerIndex p i) := by
  ext e
  simp only [originalActivityTailEvent, rawActivityTailEvent, Set.mem_ofPred_eq,
    Set.mem_iUnion, Set.mem_preimage, rawActivityPrefixCount,
    originalActivityPrefixCount, originalActivityCoin, rawActivityValue,
    profileActivityValue, profileActivityCoin, coinToReal,
    BootstrapPhysicalInput.sourceFollowerIndex]

theorem extendedActivityTailEvent_eq_raw_preimage (p : Parameters)
    (i : ActiveRoundActions.Follower p.m) :
    extendedActivityTailEvent p i =
      (fun x : ExtendedPrivateCoordinates p => x.1.1) ⁻¹'
        rawActivityTailEvent p (BootstrapPhysicalInput.sourceFollowerIndex p i) := by
  ext x
  simp only [extendedActivityTailEvent, rawActivityTailEvent, Set.mem_ofPred_eq,
    Set.mem_iUnion, Set.mem_preimage, rawActivityPrefixCount,
    extendedActivityPrefixCount, rawActivityValue, profileActivityValue,
    profileActivityCoin, coinToReal]

theorem measurable_originalActivityTailEvent (p : Parameters)
    (i : ActiveRoundActions.Follower p.m) :
    MeasurableSet (originalActivityTailEvent p i) := by
  rw [originalActivityTailEvent_eq_raw_preimage]
  exact (measurable_rawActivityTailEvent p
    (BootstrapPhysicalInput.sourceFollowerIndex p i)).preimage
      (measurable_fst.comp (measurable_fst.comp measurable_snd))

theorem measurable_extendedActivityTailEvent (p : Parameters)
    (i : ActiveRoundActions.Follower p.m) :
    MeasurableSet (extendedActivityTailEvent p i) := by
  rw [extendedActivityTailEvent_eq_raw_preimage]
  exact (measurable_rawActivityTailEvent p
    (BootstrapPhysicalInput.sourceFollowerIndex p i)).preimage
      (measurable_fst.comp measurable_fst)

/-- Pointwise bridge to the existing state-dependent block sampler.  Its
activity field is the same original first scalar for every positive numerator
profile; no law conditional on an adaptive history is asserted. -/
theorem blockDrawProfileMap_activity_originalCoin (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ (j : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (n j) a)
    (v : Fin (n_boot p) → Fin (p.m - 1) → BlockScalars)
    (s : Fin (n_boot p)) (i : ActiveRoundActions.Follower p.m) :
    (PrivateSourceStreams.blockDrawProfileMap p n hn (v s)
      (BootstrapPhysicalInput.sourceFollowerIndex p i)).1 =
      PrivateSourceStreams.activityScalarDraw p
        (((v s) (BootstrapPhysicalInput.sourceFollowerIndex p i)).1) := rfl

theorem originalFollowerBlocks_measurePreserving (p : Parameters) :
    MeasurePreserving (fun e : Coordinates p => e.2.1.1)
      (GeneratedBootstrapRoundLaw.originalLaw p) (followerBlockInputsLaw p) := by
  have hrow : MeasurePreserving Prod.snd
      (GeneratedBootstrapRoundLaw.originalLaw p) (extendedPrivateLaw p) := by
    change MeasurePreserving Prod.snd
      ((completeRowMeasure p).prod (extendedPrivateLaw p)) (extendedPrivateLaw p)
    exact measurePreserving_snd
  have hsource : MeasurePreserving Prod.fst
      (extendedPrivateLaw p) (PrivateSourceStreams.privateCoordinatesLaw p) :=
    measurePreserving_fst
  have hbase : MeasurePreserving Prod.fst
      (PrivateSourceStreams.privateCoordinatesLaw p) (followerBlockInputsLaw p) :=
    measurePreserving_fst
  have htotal := (hbase.comp hsource).comp hrow
  change MeasurePreserving (fun e : Coordinates p => e.2.1.1)
    (GeneratedBootstrapRoundLaw.originalLaw p) (followerBlockInputsLaw p) at htotal
  exact htotal

theorem originalFollowerBlocks_map (p : Parameters) :
    (GeneratedBootstrapRoundLaw.originalLaw p).map
      (fun e : Coordinates p => e.2.1.1) = followerBlockInputsLaw p :=
  (originalFollowerBlocks_measurePreserving p).map_eq

theorem extendedPrivateFollowerBlocks_measurePreserving (p : Parameters) :
    MeasurePreserving (fun x : ExtendedPrivateCoordinates p => x.1.1)
      (extendedPrivateLaw p) (followerBlockInputsLaw p) := by
  have hsource : MeasurePreserving Prod.fst
      (extendedPrivateLaw p) (PrivateSourceStreams.privateCoordinatesLaw p) :=
    measurePreserving_fst
  have hbase : MeasurePreserving Prod.fst
      (PrivateSourceStreams.privateCoordinatesLaw p) (followerBlockInputsLaw p) :=
    measurePreserving_fst
  have htotal := hbase.comp hsource
  change MeasurePreserving (fun x : ExtendedPrivateCoordinates p => x.1.1)
    (extendedPrivateLaw p) (followerBlockInputsLaw p) at htotal
  exact htotal

theorem extendedPrivateFollowerBlocks_map (p : Parameters) :
    (extendedPrivateLaw p).map (fun x : ExtendedPrivateCoordinates p => x.1.1) =
      followerBlockInputsLaw p :=
  (extendedPrivateFollowerBlocks_measurePreserving p).map_eq

theorem originalActivityPrefixCount_eq_raw (p : Parameters)
    (i : ActiveRoundActions.Follower p.m)
    (r : ℕ) (e : Coordinates p) :
    originalActivityPrefixCount p i r e =
      rawActivityPrefixCount p (BootstrapPhysicalInput.sourceFollowerIndex p i)
        r (e.2.1.1) := rfl

theorem extendedActivityPrefixCount_eq_raw (p : Parameters)
    (i : ActiveRoundActions.Follower p.m)
    (r : ℕ) (x : ExtendedPrivateCoordinates p) :
    extendedActivityPrefixCount p i r x =
      rawActivityPrefixCount p (BootstrapPhysicalInput.sourceFollowerIndex p i)
        r (x.1.1) := rfl

theorem original_activity_prefix_tail (p : Parameters)
    (i : ActiveRoundActions.Follower p.m) :
    (GeneratedBootstrapRoundLaw.originalLaw p).real (originalActivityTailEvent p i) ≤
      Real.exp (-(4 * (b_N p : ℝ))) := by
  rw [originalActivityTailEvent_eq_raw_preimage]
  have hmeasure := (originalFollowerBlocks_measurePreserving p).measure_preimage
    (measurable_rawActivityTailEvent p
      (BootstrapPhysicalInput.sourceFollowerIndex p i)).nullMeasurableSet
  change ((GeneratedBootstrapRoundLaw.originalLaw p)
      ((fun e : Coordinates p => e.2.1.1) ⁻¹'
        rawActivityTailEvent p (BootstrapPhysicalInput.sourceFollowerIndex p i))).toReal ≤ _
  rw [hmeasure]
  exact rawActivity_prefix_tail p (BootstrapPhysicalInput.sourceFollowerIndex p i)

theorem extended_private_activity_prefix_tail (p : Parameters)
    (i : ActiveRoundActions.Follower p.m) :
    (extendedPrivateLaw p).real (extendedActivityTailEvent p i) ≤
      Real.exp (-(4 * (b_N p : ℝ))) := by
  rw [extendedActivityTailEvent_eq_raw_preimage]
  have hmeasure := (extendedPrivateFollowerBlocks_measurePreserving p).measure_preimage
    (measurable_rawActivityTailEvent p
      (BootstrapPhysicalInput.sourceFollowerIndex p i)).nullMeasurableSet
  change ((extendedPrivateLaw p)
      ((fun x : ExtendedPrivateCoordinates p => x.1.1) ⁻¹'
        rawActivityTailEvent p (BootstrapPhysicalInput.sourceFollowerIndex p i))).toReal ≤ _
  rw [hmeasure]
  exact rawActivity_prefix_tail p (BootstrapPhysicalInput.sourceFollowerIndex p i)

theorem fixed_public_private_activity_prefix_tail (p : Parameters)
    (published : CompletePublicTable.PublishedOutput p)
    (rewards : FiniteBanditModel.RewardMatrix p.T p.K)
    (i : ActiveRoundActions.Follower p.m) :
    (BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p published rewards).real
      (extendedActivityTailEvent p i) ≤
      Real.exp (-(4 * (b_N p : ℝ))) := by
  change (extendedPrivateLaw p).real (extendedActivityTailEvent p i) ≤ _
  exact extended_private_activity_prefix_tail p i

end Bandits.Support.GeneratedLatentActivityTail

end
