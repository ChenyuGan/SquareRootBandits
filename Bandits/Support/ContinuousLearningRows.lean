/-
Copyright (c) 2026 Bandits Lean preparation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ContinuousControlSlice
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.AffineChannelLaw
public import Bandits.Support.OrdinaryMessageCodec
import Mathlib.Probability.Independence.InfinitePi

/-!
# Finite continuous learning/control rows

Literal learning/control component of
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`: every time
reserves the complete continuous scalar slice and both directions' affine
samples for every follower, even on unused branches. Times and rows carry
actual finite product measures. Direction `0` denotes DOWN and `1` denotes UP;
follower index `i` denotes source follower `i.val + 1`.

Freshness below concerns the vector of **all strictly earlier time controls**.
It is relevant to the history in `04_slow_fast_learner.tex:142-150`, but using
it for a protocol history requires proving that history is a measurable
function of that vector (and dealing separately with any other inputs).

This is only the learning/control component. It contains no bootstrap
dimensions, ID array, forward arrays or private post-reward row index. The
independence required when assembling those objects in
`07_public_setup.tex:11-25` remains an assembly obligation. No reference
execution, adaptive conditional law, whole-row concentration or regret claim
from `08_main_theorem.tex:26-42` is asserted here.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ContinuousLearningRows

open MeasureTheory ProbabilityTheory

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Scalar := ContinuousControlSlice.Scalar
abbrev Label (p : Parameters) := ContinuousControlSlice.Label p.m p.K
abbrev Slice (p : Parameters) := ContinuousControlSlice.Slice p.m p.K

/-- Number of followers; no independent dimension input is introduced. -/
def d (p : Parameters) : ℕ := p.m - 1

/-- The ordinary message width from the accepted codec and denominator. -/
def B (p : Parameters) : ℕ :=
  5 * OrdinaryMessageCodec.fieldWidth p.T (ConstructorDimensions.D p)

/-- DOWN/UP and every follower, including channels that are never read. -/
abbrev Channel (p : Parameters) := Fin 2 × Fin (d p)
abbrev AffineSamples (p : Parameters) := Channel p → AffineChannelLaw.Sample (B p)

/-- One full continuous slice and the full family of coefficient/offset pairs. -/
abbrev TimeControl (p : Parameters) := Slice p × AffineSamples p

/-- All `T` reserved calendar times in one learning/control row. -/
abbrev LearningRow (p : Parameters) := Fin p.T → TimeControl p

/-- All learning/control rows, with the accepted literal row count. -/
abbrev LearningRows (p : Parameters) := Fin (ConstructorDimensions.M p) → LearningRow p

def affineSamplesLaw (p : Parameters) : Measure (AffineSamples p) :=
  Measure.pi (fun _ : Channel p => (AffineChannelLaw.jointLaw (B p)).toMeasure)

def timeControlLaw (p : Parameters) : Measure (TimeControl p) :=
  (ContinuousControlSlice.sliceLaw p.m p.K).prod (affineSamplesLaw p)

def learningRowLaw (p : Parameters) : Measure (LearningRow p) :=
  Measure.pi (fun _ : Fin p.T => timeControlLaw p)

def learningRowsLaw (p : Parameters) : Measure (LearningRows p) :=
  Measure.pi (fun _ : Fin (ConstructorDimensions.M p) => learningRowLaw p)

instance affineSamplesLaw_probability (p : Parameters) :
    IsProbabilityMeasure (affineSamplesLaw p) := by
  unfold affineSamplesLaw
  infer_instance

instance timeControlLaw_probability (p : Parameters) :
    IsProbabilityMeasure (timeControlLaw p) := by
  unfold timeControlLaw
  infer_instance

instance learningRowLaw_probability (p : Parameters) :
    IsProbabilityMeasure (learningRowLaw p) := by
  unfold learningRowLaw
  infer_instance

instance learningRowsLaw_probability (p : Parameters) :
    IsProbabilityMeasure (learningRowsLaw p) := by
  unfold learningRowsLaw
  infer_instance

/-! The next two private helpers pull independence back along an actual
measure-preserving map. Their independence input is always discharged below
from product laws; it is never a premise of a learning/control result. -/

private theorem indepFun_pullback {Ω Ω' X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure Ω} {ν : Measure Ω'} {g : Ω → Ω'}
    (hg : MeasurePreserving g μ ν) {f : Ω' → X} {k : Ω' → Y}
    (hf : Measurable f) (hk : Measurable k) (h : IndepFun f k ν) :
    IndepFun (f ∘ g) (k ∘ g) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have hst := h s t hs ht
  rw [← hg.map_eq, Measure.map_apply hg.measurable ((hf hs).inter (hk ht)),
    Measure.map_apply hg.measurable (hf hs),
    Measure.map_apply hg.measurable (hk ht)] at hst
  exact hst

private theorem iIndepFun_pullback {ι Ω Ω' X : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {g : Ω → Ω'} (hg : MeasurePreserving g μ ν) {f : ι → Ω' → X}
    (hf : ∀ i, Measurable (f i)) (h : iIndepFun f ν) :
    iIndepFun (fun i => f i ∘ g) μ := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((hf i).comp hg.measurable).aemeasurable)).mpr
  have hmap : μ.map (fun ω i => f i (g ω)) = ν.map (fun ω i => f i ω) := by
    rw [← hg.map_eq, Measure.map_map (measurable_pi_iff.mpr hf) hg.measurable]
    rfl
  change μ.map (fun ω i => f i (g ω)) = Measure.pi (fun i => μ.map (f i ∘ g))
  rw [hmap, h.map_fun_eq_pi_map (fun i => (hf i).aemeasurable)]
  congr 1
  funext i
  rw [← hg.map_eq, Measure.map_map (hf i) hg.measurable]

theorem measurePreserving_slice (p : Parameters) :
    MeasurePreserving (Prod.fst : TimeControl p → Slice p)
      (timeControlLaw p) (ContinuousControlSlice.sliceLaw p.m p.K) :=
  measurePreserving_fst

theorem map_slice (p : Parameters) :
    (timeControlLaw p).map Prod.fst = ContinuousControlSlice.sliceLaw p.m p.K :=
  (measurePreserving_slice p).map_eq

theorem measurePreserving_affineSamples (p : Parameters) :
    MeasurePreserving (Prod.snd : TimeControl p → AffineSamples p)
      (timeControlLaw p) (affineSamplesLaw p) :=
  measurePreserving_snd

theorem map_affineSamples (p : Parameters) :
    (timeControlLaw p).map Prod.snd = affineSamplesLaw p :=
  (measurePreserving_affineSamples p).map_eq

theorem measurePreserving_affineSample (p : Parameters) (h : Channel p) :
    MeasurePreserving (fun x : TimeControl p => x.2 h) (timeControlLaw p)
      (AffineChannelLaw.jointLaw (B p)).toMeasure :=
  (measurePreserving_eval _ h).comp (measurePreserving_affineSamples p)

theorem map_affineSample (p : Parameters) (h : Channel p) :
    (timeControlLaw p).map (fun x => x.2 h) =
      (AffineChannelLaw.jointLaw (B p)).toMeasure :=
  (measurePreserving_affineSample p h).map_eq

/-- The whole scalar slice is independent of the whole affine vector. -/
theorem indepFun_slice_affineSamples (p : Parameters) :
    IndepFun (Prod.fst : TimeControl p → Slice p) Prod.snd (timeControlLaw p) :=
  indepFun_prod measurable_id measurable_id

theorem iIndepFun_affineSample (p : Parameters) :
    iIndepFun (fun h : Channel p => fun x : TimeControl p => x.2 h)
      (timeControlLaw p) :=
  iIndepFun_pullback (measurePreserving_affineSamples p)
    (fun h => measurable_pi_apply h) (iIndepFun_pi (fun _ => aemeasurable_id))

def controlAt {p : Parameters} (t : Fin p.T) (r : LearningRow p) : TimeControl p := r t
def sliceAt {p : Parameters} (t : Fin p.T) (r : LearningRow p) : Slice p := (r t).1
def affinesAt {p : Parameters} (t : Fin p.T) (r : LearningRow p) : AffineSamples p := (r t).2
def affineAt {p : Parameters} (t : Fin p.T) (h : Channel p) (r : LearningRow p) :
    AffineChannelLaw.Sample (B p) := (r t).2 h
def scalarAt {p : Parameters} (t : Fin p.T) (c : Label p) (r : LearningRow p) : Scalar :=
  (r t).1 c

theorem measurable_controlAt {p : Parameters} (t : Fin p.T) : Measurable (controlAt t) :=
  measurable_pi_apply t
theorem measurable_sliceAt {p : Parameters} (t : Fin p.T) : Measurable (sliceAt t) :=
  measurable_fst.comp (measurable_controlAt t)
theorem measurable_affinesAt {p : Parameters} (t : Fin p.T) : Measurable (affinesAt t) :=
  measurable_snd.comp (measurable_controlAt t)
theorem measurable_affineAt {p : Parameters} (t : Fin p.T) (h : Channel p) :
    Measurable (affineAt t h) :=
  (measurable_pi_apply h).comp (measurable_affinesAt t)
theorem measurable_scalarAt {p : Parameters} (t : Fin p.T) (c : Label p) :
    Measurable (scalarAt t c) :=
  (measurable_pi_apply c).comp (measurable_sliceAt t)

theorem measurePreserving_controlAt {p : Parameters} (t : Fin p.T) :
    MeasurePreserving (controlAt t) (learningRowLaw p) (timeControlLaw p) :=
  measurePreserving_eval _ t
theorem map_controlAt {p : Parameters} (t : Fin p.T) :
    (learningRowLaw p).map (controlAt t) = timeControlLaw p :=
  (measurePreserving_controlAt t).map_eq
theorem measurePreserving_sliceAt {p : Parameters} (t : Fin p.T) :
    MeasurePreserving (sliceAt t) (learningRowLaw p)
      (ContinuousControlSlice.sliceLaw p.m p.K) :=
  (measurePreserving_slice p).comp (measurePreserving_controlAt t)
theorem map_sliceAt {p : Parameters} (t : Fin p.T) :
    (learningRowLaw p).map (sliceAt t) = ContinuousControlSlice.sliceLaw p.m p.K :=
  (measurePreserving_sliceAt t).map_eq
theorem measurePreserving_affinesAt {p : Parameters} (t : Fin p.T) :
    MeasurePreserving (affinesAt t) (learningRowLaw p) (affineSamplesLaw p) :=
  (measurePreserving_affineSamples p).comp (measurePreserving_controlAt t)
theorem map_affinesAt {p : Parameters} (t : Fin p.T) :
    (learningRowLaw p).map (affinesAt t) = affineSamplesLaw p :=
  (measurePreserving_affinesAt t).map_eq
theorem measurePreserving_affineAt {p : Parameters} (t : Fin p.T) (h : Channel p) :
    MeasurePreserving (affineAt t h) (learningRowLaw p)
      (AffineChannelLaw.jointLaw (B p)).toMeasure :=
  (measurePreserving_affineSample p h).comp (measurePreserving_controlAt t)
theorem map_affineAt {p : Parameters} (t : Fin p.T) (h : Channel p) :
    (learningRowLaw p).map (affineAt t h) = (AffineChannelLaw.jointLaw (B p)).toMeasure :=
  (measurePreserving_affineAt t h).map_eq
theorem measurePreserving_scalarAt {p : Parameters} (t : Fin p.T) (c : Label p) :
    MeasurePreserving (scalarAt t c) (learningRowLaw p) ContinuousControlSlice.scalarLaw :=
  (ContinuousControlSlice.measurePreserving_coordinate c).comp (measurePreserving_sliceAt t)
theorem map_scalarAt {p : Parameters} (t : Fin p.T) (c : Label p) :
    (learningRowLaw p).map (scalarAt t c) = ContinuousControlSlice.scalarLaw :=
  (measurePreserving_scalarAt t c).map_eq

theorem iIndepFun_controlAt (p : Parameters) :
    iIndepFun (fun t : Fin p.T => controlAt t) (learningRowLaw p) :=
  iIndepFun_pi (fun _ => aemeasurable_id)

theorem indepFun_controlAt {p : Parameters} {s t : Fin p.T} (hst : s ≠ t) :
    IndepFun (controlAt s) (controlAt t) (learningRowLaw p) :=
  (iIndepFun_controlAt p).indepFun hst

theorem indepFun_sliceAt_affinesAt {p : Parameters} (t : Fin p.T) :
    IndepFun (sliceAt t) (affinesAt t) (learningRowLaw p) :=
  indepFun_pullback (measurePreserving_controlAt t) measurable_fst measurable_snd
    (indepFun_slice_affineSamples p)

/-- Joint independence over time and label, derived by grouping whole slices. -/
theorem iIndepFun_scalarAt (p : Parameters) :
    iIndepFun (fun i : Fin p.T × Label p => scalarAt i.1 i.2) (learningRowLaw p) := by
  apply iIndepFun_uncurry' (fun t c => measurable_scalarAt t c)
  · exact (iIndepFun_controlAt p).comp (fun _ => Prod.fst) (fun _ => measurable_fst)
  · intro t
    exact iIndepFun_pullback (measurePreserving_sliceAt t)
      (fun c => ContinuousControlSlice.measurable_coordinate c)
      (ContinuousControlSlice.iIndepFun_coordinate p.m p.K)

/-- Joint independence over every time, direction and follower. -/
theorem iIndepFun_affineAt (p : Parameters) :
    iIndepFun (fun i : Fin p.T × Channel p => affineAt i.1 i.2) (learningRowLaw p) := by
  apply iIndepFun_uncurry' (fun t h => measurable_affineAt t h)
  · exact (iIndepFun_controlAt p).comp (fun _ => Prod.snd) (fun _ => measurable_snd)
  · intro t
    exact iIndepFun_pullback (measurePreserving_affinesAt t)
      (fun h => measurable_pi_apply h) (iIndepFun_pi (fun _ => aemeasurable_id))

/-- The strict past has only valid earlier indices, with no filled suffix. -/
abbrev PastIndex {p : Parameters} (t : Fin p.T) := {s : Fin p.T // s < t}
abbrev Past {p : Parameters} (t : Fin p.T) := PastIndex t → TimeControl p

def past {p : Parameters} (t : Fin p.T) (r : LearningRow p) : Past t := fun s => r s.val
def pastLaw {p : Parameters} (t : Fin p.T) : Measure (Past t) :=
  Measure.pi (fun _ : PastIndex t => timeControlLaw p)

instance pastLaw_probability {p : Parameters} (t : Fin p.T) :
    IsProbabilityMeasure (pastLaw t) := by
  unfold pastLaw
  infer_instance

theorem measurable_past {p : Parameters} (t : Fin p.T) : Measurable (past t) :=
  measurable_pi_iff.mpr (fun s => measurable_controlAt s.val)

theorem map_past {p : Parameters} (t : Fin p.T) :
    (learningRowLaw p).map (past t) = pastLaw t := by
  change (learningRowLaw p).map (fun r (s : PastIndex t) => controlAt s.val r) =
    Measure.pi (fun _ : PastIndex t => timeControlLaw p)
  have h := (iIndepFun_controlAt p).precomp
    (g := (Subtype.val : PastIndex t → Fin p.T)) Subtype.val_injective
  simpa only [map_controlAt] using
    h.map_fun_eq_pi_map (fun s : PastIndex t => (measurable_controlAt s.val).aemeasurable)

theorem measurePreserving_past {p : Parameters} (t : Fin p.T) :
    MeasurePreserving (past t) (learningRowLaw p) (pastLaw t) :=
  ⟨measurable_past t, map_past t⟩

/-- Chronological freshness of the entire current control relative to the
entire strict past, including every earlier scalar and affine sample. -/
theorem indepFun_controlAt_past {p : Parameters} (t : Fin p.T) :
    IndepFun (controlAt t) (past t) (learningRowLaw p) := by
  have hd : Disjoint ({t} : Set (Fin p.T)) {s | s < t} := by
    refine Set.disjoint_left.mpr ?_
    intro s hs hst
    exact (ne_of_lt hst) (Set.mem_singleton_iff.mp hs)
  have h := (iIndepFun_controlAt p).indepFun_set {t} {s | s < t} hd
    (fun s => measurable_controlAt s)
  exact h.comp (measurable_pi_apply (⟨t, Set.mem_singleton t⟩ : {s // s ∈ ({t} : Set _)}))
    measurable_id

/-- The consumer supplies only measurability of its function on the actual
strict-past vector, rather than an independence or history premise. -/
theorem indepFun_controlAt_past_function {p : Parameters} (t : Fin p.T)
    {X : Type*} [MeasurableSpace X] (f : Past t → X) (hf : Measurable f) :
    IndepFun (controlAt t) (fun r => f (past t r)) (learningRowLaw p) :=
  (indepFun_controlAt_past t).comp measurable_id hf

theorem indepFun_sliceAt_past_function {p : Parameters} (t : Fin p.T)
    {X : Type*} [MeasurableSpace X] (f : Past t → X) (hf : Measurable f) :
    IndepFun (sliceAt t) (fun r => f (past t r)) (learningRowLaw p) :=
  (indepFun_controlAt_past t).comp measurable_fst hf

theorem indepFun_affineAt_past_function {p : Parameters} (t : Fin p.T) (h : Channel p)
    {X : Type*} [MeasurableSpace X] (f : Past t → X) (hf : Measurable f) :
    IndepFun (affineAt t h) (fun r => f (past t r)) (learningRowLaw p) :=
  (indepFun_controlAt_past t).comp ((measurable_pi_apply h).comp measurable_snd) hf

/-! ## Whole streams in one row -/

abbrev RowScalarIndex (p : Parameters) := Fin p.T × Label p
abbrev RowAffineIndex (p : Parameters) := Fin p.T × Channel p

def scalarStream {p : Parameters} (r : LearningRow p) : RowScalarIndex p → Scalar :=
  fun i => scalarAt i.1 i.2 r
def affineStream {p : Parameters} (r : LearningRow p) :
    RowAffineIndex p → AffineChannelLaw.Sample (B p) := fun i => affineAt i.1 i.2 r

def scalarStreamLaw (p : Parameters) : Measure (RowScalarIndex p → Scalar) :=
  Measure.pi (fun _ : RowScalarIndex p => ContinuousControlSlice.scalarLaw)
def affineStreamLaw (p : Parameters) :
    Measure (RowAffineIndex p → AffineChannelLaw.Sample (B p)) :=
  Measure.pi (fun _ : RowAffineIndex p => (AffineChannelLaw.jointLaw (B p)).toMeasure)

instance scalarStreamLaw_probability (p : Parameters) :
    IsProbabilityMeasure (scalarStreamLaw p) := by
  unfold scalarStreamLaw
  infer_instance
instance affineStreamLaw_probability (p : Parameters) :
    IsProbabilityMeasure (affineStreamLaw p) := by
  unfold affineStreamLaw
  infer_instance

theorem measurable_scalarStream (p : Parameters) :
    Measurable (scalarStream : LearningRow p → _) :=
  measurable_pi_iff.mpr (fun i => measurable_scalarAt i.1 i.2)
theorem measurable_affineStream (p : Parameters) :
    Measurable (affineStream : LearningRow p → _) :=
  measurable_pi_iff.mpr (fun i => measurable_affineAt i.1 i.2)

/-- Full continuous vector law, not just a list of marginal laws. -/
theorem map_scalarStream (p : Parameters) :
    (learningRowLaw p).map scalarStream = scalarStreamLaw p := by
  change (learningRowLaw p).map (fun r (i : RowScalarIndex p) => scalarAt i.1 i.2 r) =
    Measure.pi (fun _ : RowScalarIndex p => ContinuousControlSlice.scalarLaw)
  simpa only [map_scalarAt] using
    (iIndepFun_scalarAt p).map_fun_eq_pi_map
      (fun i : RowScalarIndex p => (measurable_scalarAt i.1 i.2).aemeasurable)
theorem measurePreserving_scalarStream (p : Parameters) :
    MeasurePreserving scalarStream (learningRowLaw p) (scalarStreamLaw p) :=
  ⟨measurable_scalarStream p, map_scalarStream p⟩

theorem map_affineStream (p : Parameters) :
    (learningRowLaw p).map affineStream = affineStreamLaw p := by
  change (learningRowLaw p).map (fun r (i : RowAffineIndex p) => affineAt i.1 i.2 r) =
    Measure.pi (fun _ : RowAffineIndex p => (AffineChannelLaw.jointLaw (B p)).toMeasure)
  simpa only [map_affineAt] using
    (iIndepFun_affineAt p).map_fun_eq_pi_map
      (fun i : RowAffineIndex p => (measurable_affineAt i.1 i.2).aemeasurable)
theorem measurePreserving_affineStream (p : Parameters) :
    MeasurePreserving affineStream (learningRowLaw p) (affineStreamLaw p) :=
  ⟨measurable_affineStream p, map_affineStream p⟩

/-- Forget endpoint proofs only; every real value remains in `[0,1)`. -/
def scalarValues {ι : Type*} (v : ι → Scalar) : ι → ℝ := fun i => (v i).val

theorem measurable_scalarValues (ι : Type*) : Measurable (scalarValues (ι := ι)) :=
  measurable_pi_iff.mpr
    (fun i => measurable_subtype_coe.comp (measurable_pi_apply i))

theorem scalarValues_mem_Ico {ι : Type*} (v : ι → Scalar) (i : ι) :
    scalarValues v i ∈ Set.Ico (0 : ℝ) 1 := (v i).property

/-- Exact real-vector law on the half-open continuous cube. -/
theorem map_scalarValues (ι : Type*) [Fintype ι] :
    (Measure.pi (fun _ : ι => ContinuousControlSlice.scalarLaw)).map scalarValues =
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict
        (Set.univ.pi (fun _ => Set.Ico 0 1)) := by
  rw [Measure.restrict_pi_pi]
  exact (measurePreserving_pi
    (fun _ : ι => ContinuousControlSlice.scalarLaw)
    (fun _ : ι => (volume : Measure ℝ).restrict (Set.Ico 0 1))
    (fun _ => ContinuousControlSlice.measurePreserving_scalar_val)).map_eq

theorem map_realScalarStream (p : Parameters) :
    (learningRowLaw p).map (fun r => scalarValues (scalarStream r)) =
      (Measure.pi (fun _ : RowScalarIndex p => (volume : Measure ℝ))).restrict
        (Set.univ.pi (fun _ => Set.Ico 0 1)) := by
  calc
    _ = ((learningRowLaw p).map scalarStream).map scalarValues :=
      (Measure.map_map (measurable_scalarValues _) (measurable_scalarStream p)).symm
    _ = _ := by
      rw [map_scalarStream]
      exact map_scalarValues _

/-- Regroup complete scalar slices and affine vectors, preserving both joint laws. -/
def splitRow {p : Parameters} (r : LearningRow p) :
    (Fin p.T → Slice p) × (Fin p.T → AffineSamples p) :=
  (fun t => (r t).1, fun t => (r t).2)

theorem measurePreserving_splitRow (p : Parameters) :
    MeasurePreserving splitRow (learningRowLaw p)
      ((Measure.pi (fun _ : Fin p.T => ContinuousControlSlice.sliceLaw p.m p.K)).prod
        (Measure.pi (fun _ : Fin p.T => affineSamplesLaw p))) :=
  measurePreserving_arrowProdEquivProdArrow (Slice p) (AffineSamples p) (Fin p.T)
    (fun _ => ContinuousControlSlice.sliceLaw p.m p.K) (fun _ => affineSamplesLaw p)

/-- The complete scalar stream is independent of the complete affine stream. -/
theorem indepFun_scalarStream_affineStream (p : Parameters) :
    IndepFun (scalarStream : LearningRow p → _) affineStream (learningRowLaw p) := by
  have h := indepFun_pullback (measurePreserving_splitRow p) measurable_fst measurable_snd
    (indepFun_prod measurable_id measurable_id)
  exact h.comp
    (measurable_pi_iff.mpr (fun i : RowScalarIndex p =>
      (measurable_pi_apply i.2).comp (measurable_pi_apply i.1)))
    (measurable_pi_iff.mpr (fun i : RowAffineIndex p =>
      (measurable_pi_apply i.2).comp (measurable_pi_apply i.1)))

/-! ## The family of rows -/

def rowAt {p : Parameters} (q : Fin (ConstructorDimensions.M p)) (r : LearningRows p) :
    LearningRow p := r q
def rowsControlAt {p : Parameters} (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (r : LearningRows p) : TimeControl p := r q t
def rowsSliceAt {p : Parameters} (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (r : LearningRows p) : Slice p := (r q t).1
def rowsAffinesAt {p : Parameters} (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (r : LearningRows p) : AffineSamples p := (r q t).2
def rowsAffineAt {p : Parameters} (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (h : Channel p) (r : LearningRows p) : AffineChannelLaw.Sample (B p) := (r q t).2 h
def rowsScalarAt {p : Parameters} (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (c : Label p) (r : LearningRows p) : Scalar := (r q t).1 c

theorem measurable_rowAt {p : Parameters} (q : Fin (ConstructorDimensions.M p)) :
    Measurable (rowAt q) := measurable_pi_apply q
theorem measurable_rowsControlAt {p : Parameters} (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) : Measurable (rowsControlAt q t) :=
  (measurable_controlAt t).comp (measurable_rowAt q)
theorem measurable_rowsSliceAt {p : Parameters} (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) : Measurable (rowsSliceAt q t) :=
  (measurable_sliceAt t).comp (measurable_rowAt q)
theorem measurable_rowsAffinesAt {p : Parameters} (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) : Measurable (rowsAffinesAt q t) :=
  (measurable_affinesAt t).comp (measurable_rowAt q)
theorem measurable_rowsAffineAt {p : Parameters} (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) (h : Channel p) : Measurable (rowsAffineAt q t h) :=
  (measurable_affineAt t h).comp (measurable_rowAt q)
theorem measurable_rowsScalarAt {p : Parameters} (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) (c : Label p) : Measurable (rowsScalarAt q t c) :=
  (measurable_scalarAt t c).comp (measurable_rowAt q)

theorem measurePreserving_rowAt {p : Parameters} (q : Fin (ConstructorDimensions.M p)) :
    MeasurePreserving (rowAt q) (learningRowsLaw p) (learningRowLaw p) :=
  measurePreserving_eval _ q
theorem map_rowAt {p : Parameters} (q : Fin (ConstructorDimensions.M p)) :
    (learningRowsLaw p).map (rowAt q) = learningRowLaw p :=
  (measurePreserving_rowAt q).map_eq
theorem measurePreserving_rowsControlAt {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    MeasurePreserving (rowsControlAt q t) (learningRowsLaw p) (timeControlLaw p) :=
  (measurePreserving_controlAt t).comp (measurePreserving_rowAt q)
theorem map_rowsControlAt {p : Parameters} (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) : (learningRowsLaw p).map (rowsControlAt q t) = timeControlLaw p :=
  (measurePreserving_rowsControlAt q t).map_eq
theorem measurePreserving_rowsSliceAt {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    MeasurePreserving (rowsSliceAt q t) (learningRowsLaw p)
      (ContinuousControlSlice.sliceLaw p.m p.K) :=
  (measurePreserving_sliceAt t).comp (measurePreserving_rowAt q)
theorem map_rowsSliceAt {p : Parameters} (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) :
    (learningRowsLaw p).map (rowsSliceAt q t) = ContinuousControlSlice.sliceLaw p.m p.K :=
  (measurePreserving_rowsSliceAt q t).map_eq
theorem measurePreserving_rowsAffinesAt {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    MeasurePreserving (rowsAffinesAt q t) (learningRowsLaw p) (affineSamplesLaw p) :=
  (measurePreserving_affinesAt t).comp (measurePreserving_rowAt q)
theorem map_rowsAffinesAt {p : Parameters} (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) : (learningRowsLaw p).map (rowsAffinesAt q t) = affineSamplesLaw p :=
  (measurePreserving_rowsAffinesAt q t).map_eq
theorem measurePreserving_rowsAffineAt {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (h : Channel p) :
    MeasurePreserving (rowsAffineAt q t h) (learningRowsLaw p)
      (AffineChannelLaw.jointLaw (B p)).toMeasure :=
  (measurePreserving_affineAt t h).comp (measurePreserving_rowAt q)
theorem map_rowsAffineAt {p : Parameters} (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) (h : Channel p) :
    (learningRowsLaw p).map (rowsAffineAt q t h) =
      (AffineChannelLaw.jointLaw (B p)).toMeasure :=
  (measurePreserving_rowsAffineAt q t h).map_eq
theorem measurePreserving_rowsScalarAt {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (c : Label p) :
    MeasurePreserving (rowsScalarAt q t c) (learningRowsLaw p) ContinuousControlSlice.scalarLaw :=
  (measurePreserving_scalarAt t c).comp (measurePreserving_rowAt q)
theorem map_rowsScalarAt {p : Parameters} (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) (c : Label p) :
    (learningRowsLaw p).map (rowsScalarAt q t c) = ContinuousControlSlice.scalarLaw :=
  (measurePreserving_rowsScalarAt q t c).map_eq

theorem iIndepFun_rowAt (p : Parameters) :
    iIndepFun (fun q : Fin (ConstructorDimensions.M p) => rowAt q) (learningRowsLaw p) :=
  iIndepFun_pi (fun _ => aemeasurable_id)

theorem indepFun_rowAt {p : Parameters} {q q' : Fin (ConstructorDimensions.M p)}
    (hqq' : q ≠ q') : IndepFun (rowAt q) (rowAt q') (learningRowsLaw p) :=
  (iIndepFun_rowAt p).indepFun hqq'

abbrev TimeIndex (p : Parameters) := Fin (ConstructorDimensions.M p) × Fin p.T
abbrev ScalarIndex (p : Parameters) := TimeIndex p × Label p
abbrev AffineIndex (p : Parameters) := TimeIndex p × Channel p

/-- Joint independence of whole time controls across rows and times. -/
theorem iIndepFun_rowsControlAt (p : Parameters) :
    iIndepFun (fun i : TimeIndex p => rowsControlAt i.1 i.2) (learningRowsLaw p) := by
  apply iIndepFun_uncurry' (fun q t => measurable_rowsControlAt q t)
  · exact iIndepFun_rowAt p
  · intro q
    exact iIndepFun_pullback (measurePreserving_rowAt q)
      (fun t => measurable_controlAt t) (iIndepFun_controlAt p)

/-- Independence of every reserved scalar, across all three indices. -/
theorem iIndepFun_rowsScalarAt (p : Parameters) :
    iIndepFun (fun i : ScalarIndex p => rowsScalarAt i.1.1 i.1.2 i.2)
      (learningRowsLaw p) := by
  apply iIndepFun_uncurry'
    (X := fun (i : TimeIndex p) (c : Label p) => rowsScalarAt i.1 i.2 c)
    (fun i c => measurable_rowsScalarAt i.1 i.2 c)
  · exact (iIndepFun_rowsControlAt p).comp (fun _ => Prod.fst) (fun _ => measurable_fst)
  · intro i
    exact iIndepFun_pullback (measurePreserving_rowsSliceAt i.1 i.2)
      (fun c => ContinuousControlSlice.measurable_coordinate c)
      (ContinuousControlSlice.iIndepFun_coordinate p.m p.K)

/-- Independence of every full affine sample, across all four indices. -/
theorem iIndepFun_rowsAffineAt (p : Parameters) :
    iIndepFun (fun i : AffineIndex p => rowsAffineAt i.1.1 i.1.2 i.2)
      (learningRowsLaw p) := by
  apply iIndepFun_uncurry'
    (X := fun (i : TimeIndex p) (h : Channel p) => rowsAffineAt i.1 i.2 h)
    (fun i h => measurable_rowsAffineAt i.1 i.2 h)
  · exact (iIndepFun_rowsControlAt p).comp (fun _ => Prod.snd) (fun _ => measurable_snd)
  · intro i
    exact iIndepFun_pullback (measurePreserving_rowsAffinesAt i.1 i.2)
      (fun h => measurable_pi_apply h) (iIndepFun_pi (fun _ => aemeasurable_id))

theorem indepFun_rowsControlAt {p : Parameters} {i j : TimeIndex p} (hij : i ≠ j) :
    IndepFun (rowsControlAt i.1 i.2) (rowsControlAt j.1 j.2) (learningRowsLaw p) :=
  (iIndepFun_rowsControlAt p).indepFun hij
theorem indepFun_rowsScalarAt {p : Parameters} {i j : ScalarIndex p} (hij : i ≠ j) :
    IndepFun (rowsScalarAt i.1.1 i.1.2 i.2) (rowsScalarAt j.1.1 j.1.2 j.2)
      (learningRowsLaw p) := (iIndepFun_rowsScalarAt p).indepFun hij
theorem indepFun_rowsAffineAt {p : Parameters} {i j : AffineIndex p} (hij : i ≠ j) :
    IndepFun (rowsAffineAt i.1.1 i.1.2 i.2) (rowsAffineAt j.1.1 j.1.2 j.2)
      (learningRowsLaw p) := (iIndepFun_rowsAffineAt p).indepFun hij

def scalarStreams {p : Parameters} (r : LearningRows p) : ScalarIndex p → Scalar :=
  fun i => rowsScalarAt i.1.1 i.1.2 i.2 r
def affineStreams {p : Parameters} (r : LearningRows p) :
    AffineIndex p → AffineChannelLaw.Sample (B p) :=
  fun i => rowsAffineAt i.1.1 i.1.2 i.2 r

def scalarStreamsLaw (p : Parameters) : Measure (ScalarIndex p → Scalar) :=
  Measure.pi (fun _ : ScalarIndex p => ContinuousControlSlice.scalarLaw)
def affineStreamsLaw (p : Parameters) :
    Measure (AffineIndex p → AffineChannelLaw.Sample (B p)) :=
  Measure.pi (fun _ : AffineIndex p => (AffineChannelLaw.jointLaw (B p)).toMeasure)

instance scalarStreamsLaw_probability (p : Parameters) :
    IsProbabilityMeasure (scalarStreamsLaw p) := by
  unfold scalarStreamsLaw
  infer_instance
instance affineStreamsLaw_probability (p : Parameters) :
    IsProbabilityMeasure (affineStreamsLaw p) := by
  unfold affineStreamsLaw
  infer_instance

theorem measurable_scalarStreams (p : Parameters) :
    Measurable (scalarStreams : LearningRows p → _) :=
  measurable_pi_iff.mpr (fun i => measurable_rowsScalarAt i.1.1 i.1.2 i.2)
theorem measurable_affineStreams (p : Parameters) :
    Measurable (affineStreams : LearningRows p → _) :=
  measurable_pi_iff.mpr (fun i => measurable_rowsAffineAt i.1.1 i.1.2 i.2)

theorem map_scalarStreams (p : Parameters) :
    (learningRowsLaw p).map scalarStreams = scalarStreamsLaw p := by
  change (learningRowsLaw p).map
    (fun r (i : ScalarIndex p) => rowsScalarAt i.1.1 i.1.2 i.2 r) =
      Measure.pi (fun _ : ScalarIndex p => ContinuousControlSlice.scalarLaw)
  simpa only [map_rowsScalarAt] using
    (iIndepFun_rowsScalarAt p).map_fun_eq_pi_map (fun i : ScalarIndex p =>
      (measurable_rowsScalarAt i.1.1 i.1.2 i.2).aemeasurable)
theorem measurePreserving_scalarStreams (p : Parameters) :
    MeasurePreserving scalarStreams (learningRowsLaw p) (scalarStreamsLaw p) :=
  ⟨measurable_scalarStreams p, map_scalarStreams p⟩

theorem map_affineStreams (p : Parameters) :
    (learningRowsLaw p).map affineStreams = affineStreamsLaw p := by
  change (learningRowsLaw p).map
    (fun r (i : AffineIndex p) => rowsAffineAt i.1.1 i.1.2 i.2 r) =
      Measure.pi (fun _ : AffineIndex p => (AffineChannelLaw.jointLaw (B p)).toMeasure)
  simpa only [map_rowsAffineAt] using
    (iIndepFun_rowsAffineAt p).map_fun_eq_pi_map (fun i : AffineIndex p =>
      (measurable_rowsAffineAt i.1.1 i.1.2 i.2).aemeasurable)
theorem measurePreserving_affineStreams (p : Parameters) :
    MeasurePreserving affineStreams (learningRowsLaw p) (affineStreamsLaw p) :=
  ⟨measurable_affineStreams p, map_affineStreams p⟩

/-- Joint real-vector law of every scalar in the entire learning component. -/
theorem map_realScalarStreams (p : Parameters) :
    (learningRowsLaw p).map (fun r => scalarValues (scalarStreams r)) =
      (Measure.pi (fun _ : ScalarIndex p => (volume : Measure ℝ))).restrict
        (Set.univ.pi (fun _ => Set.Ico 0 1)) := by
  calc
    _ = ((learningRowsLaw p).map scalarStreams).map scalarValues :=
      (Measure.map_map (measurable_scalarValues _) (measurable_scalarStreams p)).symm
    _ = _ := by
      rw [map_scalarStreams]
      exact map_scalarValues _

/-- Joint independence also holds for the actual real-valued coordinates. -/
theorem iIndepFun_realScalarStreams (p : Parameters) :
    iIndepFun (fun i : ScalarIndex p => fun r : LearningRows p =>
      (rowsScalarAt i.1.1 i.1.2 i.2 r).val) (learningRowsLaw p) :=
  (iIndepFun_rowsScalarAt p).comp (fun _ => Subtype.val) (fun _ => measurable_subtype_coe)

/-! ## Freshness in the actual row-family probability space -/

def rowsPast {p : Parameters} (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (r : LearningRows p) : Past t := past t (r q)

theorem measurable_rowsPast {p : Parameters} (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) : Measurable (rowsPast q t) :=
  (measurable_past t).comp (measurable_rowAt q)
theorem measurePreserving_rowsPast {p : Parameters} (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) : MeasurePreserving (rowsPast q t) (learningRowsLaw p) (pastLaw t) :=
  (measurePreserving_past t).comp (measurePreserving_rowAt q)
theorem map_rowsPast {p : Parameters} (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    (learningRowsLaw p).map (rowsPast q t) = pastLaw t :=
  (measurePreserving_rowsPast q t).map_eq

theorem indepFun_rowsControlAt_rowsPast {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    IndepFun (rowsControlAt q t) (rowsPast q t) (learningRowsLaw p) :=
  indepFun_pullback (measurePreserving_rowAt q) (measurable_controlAt t)
    (measurable_past t) (indepFun_controlAt_past t)

theorem indepFun_rowsSliceAt_rowsAffinesAt {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    IndepFun (rowsSliceAt q t) (rowsAffinesAt q t) (learningRowsLaw p) :=
  indepFun_pullback (measurePreserving_rowAt q) (measurable_sliceAt t)
    (measurable_affinesAt t) (indepFun_sliceAt_affinesAt t)

theorem indepFun_rowsControlAt_past_function {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    {X : Type*} [MeasurableSpace X] (f : Past t → X) (hf : Measurable f) :
    IndepFun (rowsControlAt q t) (fun r => f (rowsPast q t r)) (learningRowsLaw p) :=
  (indepFun_rowsControlAt_rowsPast q t).comp measurable_id hf

theorem indepFun_rowsSliceAt_past_function {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    {X : Type*} [MeasurableSpace X] (f : Past t → X) (hf : Measurable f) :
    IndepFun (rowsSliceAt q t) (fun r => f (rowsPast q t r)) (learningRowsLaw p) :=
  (indepFun_rowsControlAt_rowsPast q t).comp measurable_fst hf

theorem indepFun_rowsAffineAt_past_function {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (h : Channel p)
    {X : Type*} [MeasurableSpace X] (f : Past t → X) (hf : Measurable f) :
    IndepFun (rowsAffineAt q t h) (fun r => f (rowsPast q t r)) (learningRowsLaw p) :=
  (indepFun_rowsControlAt_rowsPast q t).comp
    ((measurable_pi_apply h).comp measurable_snd) hf

/-! ## Grouping all scalar streams against all affine streams -/

/-- Regroup the actual product coordinates; no randomness is identified or shared. -/
def splitRows {p : Parameters} (r : LearningRows p) :
    (Fin (ConstructorDimensions.M p) → Fin p.T → Slice p) ×
      (Fin (ConstructorDimensions.M p) → Fin p.T → AffineSamples p) :=
  (fun q t => (r q t).1, fun q t => (r q t).2)

theorem measurePreserving_splitRows (p : Parameters) :
    MeasurePreserving splitRows (learningRowsLaw p)
      ((Measure.pi (fun _ : Fin (ConstructorDimensions.M p) =>
        Measure.pi (fun _ : Fin p.T => ContinuousControlSlice.sliceLaw p.m p.K))).prod
        (Measure.pi (fun _ : Fin (ConstructorDimensions.M p) =>
          Measure.pi (fun _ : Fin p.T => affineSamplesLaw p)))) := by
  exact (measurePreserving_arrowProdEquivProdArrow
    (Fin p.T → Slice p) (Fin p.T → AffineSamples p) (Fin (ConstructorDimensions.M p))
    (fun _ => Measure.pi (fun _ : Fin p.T => ContinuousControlSlice.sliceLaw p.m p.K))
    (fun _ => Measure.pi (fun _ : Fin p.T => affineSamplesLaw p))).comp
      (measurePreserving_pi (fun _ : Fin (ConstructorDimensions.M p) => learningRowLaw p)
        (fun _ => (Measure.pi (fun _ : Fin p.T =>
          ContinuousControlSlice.sliceLaw p.m p.K)).prod
            (Measure.pi (fun _ : Fin p.T => affineSamplesLaw p)))
        (fun _ => measurePreserving_splitRow p))

/-- All scalar coordinates jointly are independent of all affine samples jointly. -/
theorem indepFun_scalarStreams_affineStreams (p : Parameters) :
    IndepFun (scalarStreams : LearningRows p → _) affineStreams (learningRowsLaw p) := by
  have h := indepFun_pullback (measurePreserving_splitRows p) measurable_fst measurable_snd
    (indepFun_prod measurable_id measurable_id)
  have hs : Measurable (fun s : Fin (ConstructorDimensions.M p) → Fin p.T → Slice p =>
      fun i : ScalarIndex p => s i.1.1 i.1.2 i.2) :=
    measurable_pi_iff.mpr (fun i : ScalarIndex p =>
      (measurable_pi_apply i.2).comp
        ((measurable_pi_apply i.1.2).comp (measurable_pi_apply i.1.1)))
  have ha : Measurable
      (fun s : Fin (ConstructorDimensions.M p) → Fin p.T → AffineSamples p =>
        fun i : AffineIndex p => s i.1.1 i.1.2 i.2) :=
    measurable_pi_iff.mpr (fun i : AffineIndex p =>
      (measurable_pi_apply i.2).comp
        ((measurable_pi_apply i.1.2).comp (measurable_pi_apply i.1.1)))
  exact h.comp hs ha

/-- Exact product of the two complete stream laws in one row. -/
theorem map_scalarStream_affineStream (p : Parameters) :
    (learningRowLaw p).map (fun r => (scalarStream r, affineStream r)) =
      (scalarStreamLaw p).prod (affineStreamLaw p) := by
  rw [(indepFun_scalarStream_affineStream p).map_prod_eq_prod_map_map
    (measurable_scalarStream p).aemeasurable (measurable_affineStream p).aemeasurable,
    map_scalarStream, map_affineStream]

/-- Exact product of the complete continuous and affine laws over the entire family. -/
theorem map_scalarStreams_affineStreams (p : Parameters) :
    (learningRowsLaw p).map (fun r => (scalarStreams r, affineStreams r)) =
      (scalarStreamsLaw p).prod (affineStreamsLaw p) := by
  rw [(indepFun_scalarStreams_affineStreams p).map_prod_eq_prod_map_map
    (measurable_scalarStreams p).aemeasurable (measurable_affineStreams p).aemeasurable,
    map_scalarStreams, map_affineStreams]

/-! ## Freshness relative to earlier controls in every row -/

/-- True finite strict past across all rows, still excluding every time `≥ t`. -/
abbrev EarlierTimeIndex {p : Parameters} (t : Fin p.T) :=
  {i : TimeIndex p // i.2 < t}
abbrev EarlierControls {p : Parameters} (t : Fin p.T) :=
  EarlierTimeIndex t → TimeControl p

def earlierControls {p : Parameters} (t : Fin p.T) (r : LearningRows p) :
    EarlierControls t := fun i => rowsControlAt i.val.1 i.val.2 r
def earlierControlsLaw {p : Parameters} (t : Fin p.T) : Measure (EarlierControls t) :=
  Measure.pi (fun _ : EarlierTimeIndex t => timeControlLaw p)

instance earlierControlsLaw_probability {p : Parameters} (t : Fin p.T) :
    IsProbabilityMeasure (earlierControlsLaw t) := by
  unfold earlierControlsLaw
  infer_instance

theorem measurable_earlierControls {p : Parameters} (t : Fin p.T) :
    Measurable (earlierControls t) :=
  measurable_pi_iff.mpr (fun i => measurable_rowsControlAt i.val.1 i.val.2)

theorem map_earlierControls {p : Parameters} (t : Fin p.T) :
    (learningRowsLaw p).map (earlierControls t) = earlierControlsLaw t := by
  change (learningRowsLaw p).map
    (fun r (i : EarlierTimeIndex t) => rowsControlAt i.val.1 i.val.2 r) =
      Measure.pi (fun _ : EarlierTimeIndex t => timeControlLaw p)
  have h := (iIndepFun_rowsControlAt p).precomp
    (g := (Subtype.val : EarlierTimeIndex t → TimeIndex p)) Subtype.val_injective
  simpa only [map_rowsControlAt] using
    h.map_fun_eq_pi_map (fun i : EarlierTimeIndex t =>
      (measurable_rowsControlAt i.val.1 i.val.2).aemeasurable)

theorem measurePreserving_earlierControls {p : Parameters} (t : Fin p.T) :
    MeasurePreserving (earlierControls t) (learningRowsLaw p) (earlierControlsLaw t) :=
  ⟨measurable_earlierControls t, map_earlierControls t⟩

/-- Even the full vector of all rows' earlier controls is independent of this
row's current entire time control. This remains an unconditional product law. -/
theorem indepFun_rowsControlAt_earlierControls {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    IndepFun (rowsControlAt q t) (earlierControls t) (learningRowsLaw p) := by
  have hd : Disjoint ({(q, t)} : Set (TimeIndex p)) {i | i.2 < t} := by
    refine Set.disjoint_left.mpr ?_
    intro i hi hit
    exact (ne_of_lt hit) (congrArg Prod.snd (Set.mem_singleton_iff.mp hi))
  have h := (iIndepFun_rowsControlAt p).indepFun_set {(q, t)} {i | i.2 < t} hd
    (fun i => measurable_rowsControlAt i.1 i.2)
  exact h.comp
    (measurable_pi_apply
      (⟨(q, t), Set.mem_singleton (q, t)⟩ : {i // i ∈ ({(q, t)} : Set (TimeIndex p))}))
    measurable_id

theorem indepFun_rowsControlAt_earlierControls_function {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    {X : Type*} [MeasurableSpace X] (f : EarlierControls t → X) (hf : Measurable f) :
    IndepFun (rowsControlAt q t) (fun r => f (earlierControls t r)) (learningRowsLaw p) :=
  (indepFun_rowsControlAt_earlierControls q t).comp measurable_id hf

theorem indepFun_rowsSliceAt_earlierControls_function {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    {X : Type*} [MeasurableSpace X] (f : EarlierControls t → X) (hf : Measurable f) :
    IndepFun (rowsSliceAt q t) (fun r => f (earlierControls t r)) (learningRowsLaw p) :=
  (indepFun_rowsControlAt_earlierControls q t).comp measurable_fst hf

theorem indepFun_rowsAffineAt_earlierControls_function {p : Parameters}
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (h : Channel p)
    {X : Type*} [MeasurableSpace X] (f : EarlierControls t → X) (hf : Measurable f) :
    IndepFun (rowsAffineAt q t h) (fun r => f (earlierControls t r)) (learningRowsLaw p) :=
  (indepFun_rowsControlAt_earlierControls q t).comp
    ((measurable_pi_apply h).comp measurable_snd) hf

end Bandits.Support.ContinuousLearningRows
