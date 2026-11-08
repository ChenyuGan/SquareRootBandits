/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePrelaunchDownInvariance
public import Bandits.Support.PrelaunchDownAffineProduct
public import Bandits.Support.InitializationFailureProvenance
public import Bandits.Support.ReferenceInitializationMeasurability
public import Mathlib.Data.Finset.Sort

/-!
# Physical prelaunch DOWN tests under the original product law

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:724-735`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:111-155`, and
`sources/zip4/manuscript/05_binary_transport.tex:7-53`.

The receiver gates and rounded rewards below come from the generated physical
history. The DOWN bank is separated from the entire remaining original row
and private coordinates by the accepted measurable equivalence. No ordinary
decoder state or decision is asserted invariant under DOWN resampling.

These results are internal, before publication conditioning. The fixed-start
event is distinguished from the literal suppressed-decision event: identifying
all ordinary completed batches with fixed-start tests is a separate obligation.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.PrelaunchDownAffineProduct
open Bandits.Support.ReferencePrelaunchDownInvariance
open Bandits.Support.AffineChannelLaw
open scoped Classical ENNReal

namespace Bandits.Support.ReferenceSuppressedDownTail

variable (p : ConstructorDimensions.Parameters) (ids : IDArray p)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
  (C_star C_h : ℝ) (eta : LearningRate)

local notation "X" => GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta

/-- The literal source event, retaining the accepted strict launch-prefix
witness and the actual carried ordinary decoder replay. -/
def E_down : Set (GeneratedBootstrapRoundLaw.Coordinates p) :=
  {e | ∃ i, ∃ s, InitializationFailureProvenance.suppressedDownAt (X e) s i}

/-- Reassemble the original complete row and private coordinates exactly. -/
def coordinates (bank : DownBank p) (side : Side p) :
    GeneratedBootstrapRoundLaw.Coordinates p :=
  (affineDownSplitEquiv p).symm (bank, side)

theorem coordinates_split (bank : DownBank p) (side : Side p) :
    affineDownSplitEquiv p (coordinates p bank side) = (bank, side) :=
  (affineDownSplitEquiv p).apply_symm_apply _

/-- Equality of complete side coordinates keeps every forward bit, every
continuous slice, every UP sample, and the original entire private coordinate. -/
theorem coordinates_agree (bank bank' : DownBank p) (side : Side p) :
    DownCoordinateAgreement (coordinates p bank side).1 (coordinates p bank' side).1 ∧
      (coordinates p bank side).2 = (coordinates p bank' side).2 := by
  have hs : (affineDownSplitEquiv p (coordinates p bank side)).2 =
      (affineDownSplitEquiv p (coordinates p bank' side)).2 := by
    rw [coordinates_split, coordinates_split]
  have hf := congrArg (fun s : Side p => s.1.1) hs
  have hp := congrArg (fun s : Side p => s.2) hs
  simp only [affineDownSplitEquiv_forward] at hf
  simp only [affineDownSplitEquiv_private] at hp
  refine ⟨⟨fun u t => congrFun (congrFun hf u) t, ?_, ?_⟩, hp⟩
  · intro t
    simpa only [affineDownSplitEquiv_slice] using
      congrArg (fun s : Side p => s.1.2.1 t) hs
  · intro t i
    simpa only [affineDownSplitEquiv_up] using
      congrArg (fun s : Side p => s.1.2.2 t i) hs

theorem input_bank_update (bank bank' : DownBank p) (side : Side p) :
    X (coordinates p bank' side) =
      {X (coordinates p bank side) with row := (coordinates p bank' side).1} := by
  have hp := (coordinates_agree p bank bank' side).2
  simp only [GeneratedBootstrapRoundLaw.input,
    ReferenceInitializationMeasurability.inputOfCoordinates]
  rw [hp]

/-- The actual generated boundary, including its physical history and
activation map, ignores all DOWN bank values simultaneously. -/
theorem run_bank_eq (bank bank' : DownBank p) (side : Side p) (r : ℕ) :
    ReferenceInitializationRun.run (X (coordinates p bank side)) r =
      ReferenceInitializationRun.run (X (coordinates p bank' side)) r := by
  rw [input_bank_update p ids rewards C_star C_h eta bank bank' side]
  exact ReferencePrelaunchDownInvariance.run_eq _ _
    (coordinates_agree p bank bank' side).1 r

theorem launchRound_bank_eq (bank bank' : DownBank p) (side : Side p) :
    ReferenceInitializationRun.launchRound (X (coordinates p bank side)) =
      ReferenceInitializationRun.launchRound (X (coordinates p bank' side)) := by
  rw [input_bank_update p ids rewards C_star C_h eta bank bank' side]
  exact ReferencePrelaunchDownInvariance.launchRound_eq _ _
    (coordinates_agree p bank bank' side).1

/-- Eligible tests from the terminal generated physical prefix, with that
same run's activation and the source's strict prelaunch endpoint. -/
def eligibleTimes (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (i : Fin (p.m - 1)) : Finset (Fin p.T) :=
  let b := ReferenceInitializationRun.output (X e)
  match b.activation (receiverFollower i) with
  | none => ∅
  | some a => (selectedPositiveTimes (X e) b i a).filter
      (fun t => t.val + 1 < ReferenceInitializationRun.launchRound (X e))

/-- Derive the activation premise from the actual output and consume the
accepted selected-positive invariance; no supplied positivity policy occurs. -/
theorem eligibleTimes_bank_eq (bank bank' : DownBank p) (side : Side p)
    (i : Fin (p.m - 1)) :
    eligibleTimes p ids rewards C_star C_h eta (coordinates p bank side) i =
      eligibleTimes p ids rewards C_star C_h eta (coordinates p bank' side) i := by
  have hb := run_bank_eq p ids rewards C_star C_h eta bank bank' side
    (BootstrapDimensions.n_boot p)
  change ReferenceInitializationRun.output (X (coordinates p bank side)) =
    ReferenceInitializationRun.output (X (coordinates p bank' side)) at hb
  have hl := launchRound_bank_eq p ids rewards C_star C_h eta bank bank' side
  unfold eligibleTimes
  dsimp only
  cases ha : (ReferenceInitializationRun.output (X (coordinates p bank side))).activation
      (receiverFollower i) with
  | none => rw [← hb, ha]
  | some a =>
    have ht := ReferencePrelaunchDownInvariance.selectedPositiveTimes_eq
      (X (coordinates p bank side)) (coordinates p bank' side).1
      (coordinates_agree p bank bank' side).1 (BootstrapDimensions.n_boot p) i a ha
    rw [← input_bank_update p ids rewards C_star C_h eta bank bank' side] at ht
    have ha' : (ReferenceInitializationRun.output (X (coordinates p bank' side))).activation
        (receiverFollower i) = some a := by rw [← hb]; exact ha
    rw [ha']
    exact congrArg₂ (fun ts l => ts.filter (fun t => t.val + 1 < l)) ht.1 hl

/-- A zero bank is used solely to evaluate a bank-independent side factor;
the reconstruction theorem removes it from every actual test identity. -/
def zeroBank : DownBank p := fun _ _ => (0, 0)

def sideEligibleTimes (side : Side p) (i : Fin (p.m - 1)) : Finset (Fin p.T) :=
  eligibleTimes p ids rewards C_star C_h eta (coordinates p (zeroBank p) side) i

theorem eligibleTimes_eq_side (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (i : Fin (p.m - 1)) :
    eligibleTimes p ids rewards C_star C_h eta e i =
      sideEligibleTimes p ids rewards C_star C_h eta (affineDownSplitEquiv p e).2 i := by
  have h := eligibleTimes_bank_eq p ids rewards C_star C_h eta
    (affineDownSplitEquiv p e).1 (zeroBank p) (affineDownSplitEquiv p e).2 i
  change eligibleTimes p ids rewards C_star C_h eta
    ((affineDownSplitEquiv p).symm (affineDownSplitEquiv p e)) i = _ at h
  simpa only [MeasurableEquiv.symm_apply_apply, sideEligibleTimes] using h

/-- Finite controls read by the existing ordinary DOWN adapter. The sample
coordinate is retained as in its accepted measurable row code. -/
abbrev RoundCode := Fin p.T → PublicDiscreteDraws.Slot ×
  (Fin (p.m - 1) × Sample (ContinuousLearningRows.B p))

/-- The actual adapter's Boolean selection is exactly its three source gates. -/
theorem downInput_selected_iff (i : Fin (p.m - 1)) (row : CompleteRow p)
    (a : Activation p) (t : Fin p.T) (own : Fin p.K × Observation p) :
    (downInput i row a t own).selected = true ↔
      a.val ≤ t.val + 1 ∧ PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i := by
  unfold downInput
  exact @decide_eq_true_iff _ _

/-- A finite-code evaluation of the literal physical eligibility filter.
The observation is still the generated boundary's own rounded observation. -/
def eligibleFromCode (b : ReferenceInitializationRun.Boundary p)
    (code : RoundCode p) (i : Fin (p.m - 1)) (launch : ℕ) : Finset (Fin p.T) :=
  match b.activation (receiverFollower i) with
  | none => ∅
  | some a => Finset.univ.filter fun t =>
      (∃ ht : t.val < ReferenceInitializationRun.elapsed p b.completed,
        (a.val ≤ t.val + 1 ∧ (code t).1 = PublicDiscreteDraws.downSlot ∧
          (code t).2.1 = i) ∧
        0 < (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m (receiverFollower i))
          ⟨t.val, ht⟩).2.val.val) ∧ t.val + 1 < launch

theorem eligibleTimes_eq_code (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (i : Fin (p.m - 1)) :
    eligibleTimes p ids rewards C_star C_h eta e i =
      eligibleFromCode p (ReferenceInitializationRun.output (X e))
        (ReferenceInitializationMeasurability.ordinaryRowCode p i e.1) i
        (ReferenceInitializationRun.launchRound (X e)) := by
  ext t
  cases ha : (ReferenceInitializationRun.output (X e)).activation (receiverFollower i) with
  | none => simp only [eligibleTimes, eligibleFromCode, ha]
  | some a =>
    simp only [eligibleTimes, eligibleFromCode, ha]
    simp [selectedPositiveTimes, downInput_selected_iff,
      ReferenceInitializationMeasurability.ordinaryRowCode, calendar,
      GeneratedBootstrapRoundLaw.input, ReferenceInitializationMeasurability.inputOfCoordinates,
      exists_and_left]
    intro _ _ _ _ _
    rfl

/-- Measurability is proved from the accepted measurable generated boundary
and finite row controls, rather than supplied as an event hypothesis. -/
theorem measurable_eligibleTimes (i : Fin (p.m - 1)) :
    Measurable (fun e => eligibleTimes p ids rewards C_star C_h eta e i) := by
  have hi : Measurable (fun e : GeneratedBootstrapRoundLaw.Coordinates p => (ids, e)) :=
    measurable_const.prodMk measurable_id
  have hb := (ReferenceInitializationMeasurability.measurable_output
    p C_star C_h eta rewards).comp hi
  have hl := (ReferenceInitializationMeasurability.measurable_launchRound
    p C_star C_h eta rewards).comp hi
  have hc : Measurable (fun e : GeneratedBootstrapRoundLaw.Coordinates p =>
      ReferenceInitializationMeasurability.ordinaryRowCode p i e.1) :=
    (ReferenceInitializationMeasurability.measurable_ordinaryRowCode p i).comp measurable_fst
  have hm := (measurable_of_countable (fun k :
      (ReferenceInitializationRun.Boundary p × RoundCode p) × ℕ =>
      eligibleFromCode p k.1.1 k.1.2 i k.2)).comp ((hb.prodMk hc).prodMk hl)
  have heq : (fun e => eligibleTimes p ids rewards C_star C_h eta e i) =
      (fun e => eligibleFromCode p (ReferenceInitializationRun.output (X e))
        (ReferenceInitializationMeasurability.ordinaryRowCode p i e.1) i
        (ReferenceInitializationRun.launchRound (X e))) :=
    funext (fun e => eligibleTimes_eq_code p ids rewards C_star C_h eta e i)
  rw [heq]
  exact hm

theorem measurable_sideEligibleTimes (i : Fin (p.m - 1)) :
    Measurable (fun side => sideEligibleTimes p ids rewards C_star C_h eta side i) :=
  (measurable_eligibleTimes p ids rewards C_star C_h eta i).comp
    ((affineDownSplitEquiv p).symm.measurable.comp (measurable_const.prodMk measurable_id))

/-- The actual eligible-test identity includes activation, generated physical
feedback and the original adapter's selected and rounded-reward fields. -/
theorem mem_eligibleTimes_iff (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    t ∈ eligibleTimes p ids rewards C_star C_h eta e i ↔
      ∃ a, (ReferenceInitializationRun.output (X e)).activation (receiverFollower i) = some a ∧
        t.val + 1 < ReferenceInitializationRun.launchRound (X e) ∧
        ∃ ht : t.val < ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output (X e)).completed,
          let own := (ReferenceInitializationRun.output (X e)).history
            (PublicDiscreteDraws.followerPlayer p.two_le_m (receiverFollower i)) ⟨t.val, ht⟩
          (downInput i e.1 a t own).selected = true ∧
            0 < (downInput i e.1 a t own).roundedReward := by
  cases ha : (ReferenceInitializationRun.output (X e)).activation (receiverFollower i) with
  | none => simp only [eligibleTimes, ha, Finset.notMem_empty, reduceCtorEq, false_and,
      exists_false]
  | some a =>
    simp only [eligibleTimes, ha]
    simp [selectedPositiveTimes, downInput, calendar, and_comm,
      GeneratedBootstrapRoundLaw.input, ReferenceInitializationMeasurability.inputOfCoordinates]

/-- All actual eligible times at or after one calendar start. This does not
reset the ordinary decoder at block boundaries. -/
def timesAfter (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (i : Fin (p.m - 1)) (start : Fin p.T) : Finset (Fin p.T) :=
  (eligibleTimes p ids rewards C_star C_h eta e i).filter (fun t => start ≤ t)

/-- The first `q` distinct chronological eligible physical tests. -/
def firstTimes (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (i : Fin (p.m - 1)) (start : Fin p.T) (q : ℕ) : List (Fin p.T) :=
  ((timesAfter p ids rewards C_star C_h eta e i start).sort (· ≤ ·)).take q

theorem firstTimes_nodup (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (i : Fin (p.m - 1)) (start : Fin p.T) (q : ℕ) :
    (firstTimes p ids rewards C_star C_h eta e i start q).Nodup :=
  ((timesAfter p ids rewards C_star C_h eta e i start).sort_nodup (· ≤ ·)).take

theorem firstTimes_length (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (i : Fin (p.m - 1)) (start : Fin p.T) (q : ℕ) :
    (firstTimes p ids rewards C_star C_h eta e i start q).length =
      min q (timesAfter p ids rewards C_star C_h eta e i start).card := by
  rw [firstTimes, List.length_take, Finset.length_sort]

theorem firstTimes_strict (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (i : Fin (p.m - 1)) (start : Fin p.T) (q : ℕ) :
    (firstTimes p ids rewards C_star C_h eta e i start q).Pairwise (· < ·) :=
  (timesAfter p ids rewards C_star C_h eta e i start).sortedLT_sort.pairwise.take

theorem mem_firstTimes_eligible (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (i : Fin (p.m - 1)) (start : Fin p.T) (q : ℕ) (t : Fin p.T)
    (ht : t ∈ firstTimes p ids rewards C_star C_h eta e i start q) :
    t ∈ eligibleTimes p ids rewards C_star C_h eta e i ∧ start ≤ t := by
  have h := ((timesAfter p ids rewards C_star C_h eta e i start).mem_sort (· ≤ ·)).mp
    (List.mem_of_mem_take ht)
  exact Finset.mem_filter.mp h

theorem measurable_timesAfter (i : Fin (p.m - 1)) (start : Fin p.T) :
    Measurable (fun e => timesAfter p ids rewards C_star C_h eta e i start) :=
  (measurable_of_countable (fun A : Finset (Fin p.T) => A.filter (fun t => start ≤ t))).comp
    (measurable_eligibleTimes p ids rewards C_star C_h eta i)

theorem measurable_firstTimes (i : Fin (p.m - 1)) (start : Fin p.T) (q : ℕ) :
    Measurable (fun e => firstTimes p ids rewards C_star C_h eta e i start q) :=
  (measurable_of_countable (fun A : Finset (Fin p.T) => (A.sort (· ≤ ·)).take q)).comp
    (measurable_timesAfter p ids rewards C_star C_h eta i start)

/-- The literal original direction-zero sample, with its follower index
written explicitly in the original channel carrier. -/
def downSample (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (t : Fin p.T) (i : Fin (p.m - 1)) : Sample (AffineBatchDecoder.width p) :=
  (e.1.2 t).2 (0, ⟨i.val, i.isLt⟩)

theorem downSample_eq_bank (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    downSample p e t i = (affineDownSplitEquiv p e).1 t i :=
  (congrFun (congrFun (affineDownSplitEquiv_bank p e) t) i).symm

/-- Each selected test really is eligible for the existing decoder, at the
generated activation and physical observation, with the original DOWN pair.
No history, rounded-reward process or selection rule is supplied by a caller. -/
theorem firstTimes_generated_test (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (i : Fin (p.m - 1)) (start : Fin p.T) (q : ℕ) (t : Fin p.T)
    (ht : t ∈ firstTimes p ids rewards C_star C_h eta e i start q) :
    ∃ a, (ReferenceInitializationRun.output (X e)).activation (receiverFollower i) = some a ∧
      ∃ h : t.val < ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output (X e)).completed,
        let own := (ReferenceInitializationRun.output (X e)).history
          (PublicDiscreteDraws.followerPlayer p.two_le_m (receiverFollower i)) ⟨t.val, h⟩
        t.val + 1 < ReferenceInitializationRun.launchRound (X e) ∧
          AffineBatchDecoder.eligible (downInput i e.1 a t own) ∧
          (downInput i e.1 a t own).sample = downSample p e t i := by
  have hm := (mem_firstTimes_eligible p ids rewards C_star C_h eta e i start q t ht).1
  obtain ⟨a, ha, hl, h, hs, hp⟩ :=
    (mem_eligibleTimes_iff p ids rewards C_star C_h eta e i t).mp hm
  exact ⟨a, ha, h, hl, ⟨hs, rfl, hp⟩, rfl⟩

/-- Source-shaped survival of the actual no-sender tests at a fixed start.
Insufficient remaining positive tests make this event false. -/
def fixedStartSurvival (i : Fin (p.m - 1)) (start : Fin p.T)
    (M : Word (AffineBatchDecoder.width p)) (q : ℕ) :
    Set (GeneratedBootstrapRoundLaw.Coordinates p) :=
  {e | q ≤ (timesAfter p ids rewards C_star C_h eta e i start).card ∧
    AffineBatchDecoder.satisfies
      ((firstTimes p ids rewards C_star C_h eta e i start q).map
        (fun t => downSample p e t i)) M}

/-- Exact accepted decoder equations, using the original row's DOWN samples
at the chronological generated eligible times. -/
theorem mem_fixedStartSurvival_iff (e : GeneratedBootstrapRoundLaw.Coordinates p)
    (i : Fin (p.m - 1)) (start : Fin p.T)
    (M : Word (AffineBatchDecoder.width p)) (q : ℕ) :
    e ∈ fixedStartSurvival p ids rewards C_star C_h eta i start M q ↔
      q ≤ (timesAfter p ids rewards C_star C_h eta e i start).card ∧
      ∀ t ∈ firstTimes p ids rewards C_star C_h eta e i start q,
        affineHash (downSample p e t i) M = 1 := by
  change (_ ∧ AffineBatchDecoder.satisfies _ M) ↔ _
  rw [AffineBatchDecoder.satisfies_iff_hashes]
  simp only [List.forall_mem_map]

theorem measurableSet_fixedStartSurvival (i : Fin (p.m - 1)) (start : Fin p.T)
    (M : Word (AffineBatchDecoder.width p)) (q : ℕ) :
    MeasurableSet (fixedStartSurvival p ids rewards C_star C_h eta i start M q) := by
  have hbank : Measurable (fun e : GeneratedBootstrapRoundLaw.Coordinates p =>
      (affineDownSplitEquiv p e).1) := measurable_fst.comp (affineDownSplitEquiv p).measurable
  have ht := measurable_timesAfter p ids rewards C_star C_h eta i start
  have hf := measurable_firstTimes p ids rewards C_star C_h eta i start q
  have hm := (measurable_of_countable (fun k :
      (Finset (Fin p.T) × List (Fin p.T)) × DownBank p =>
      q ≤ k.1.1.card ∧ ∀ t ∈ k.1.2, affineHash (k.2 t i) M = 1)).comp
        ((ht.prodMk hf).prodMk hbank)
  have heq : fixedStartSurvival p ids rewards C_star C_h eta i start M q =
      {e | q ≤ (timesAfter p ids rewards C_star C_h eta e i start).card ∧
        ∀ t ∈ firstTimes p ids rewards C_star C_h eta e i start q,
          affineHash ((affineDownSplitEquiv p e).1 t i) M = 1} := by
    ext e
    simp only [mem_fixedStartSurvival_iff, Set.mem_ofPred_eq, downSample_eq_bank]
    rfl
  rw [heq]
  exact measurableSet_setOfPred.mpr hm

/-- A fixed distinct set of original DOWN coordinates obeys the exact
one-half product law; all other followers and all other rounds remain free. -/
theorem bank_equations_probability (i : Fin (p.m - 1))
    (A : Finset (Fin p.T)) (M : Word (AffineBatchDecoder.width p)) :
    downBankLaw p {bank | ∀ t ∈ A, affineHash (bank t i) M = 1} =
      ((1 : ℝ≥0∞) / 2) ^ A.card := by
  have hone : downAtTimeLaw p {v | affineHash (v i) M = 1} = (1 : ℝ≥0∞) / 2 := by
    change Word (ContinuousLearningRows.B p) at M
    have heval := measurePreserving_eval
      (fun _ : Fin (p.m - 1) => (jointLaw (ContinuousLearningRows.B p)).toMeasure) i
    rw [← affineHash_probability M (1 : Bit), eventProbability_eq_measure]
    exact heval.measure_preimage (s := {s | affineHash s M = 1})
      MeasurableSet.of_discrete.nullMeasurableSet
  change Measure.pi (fun _ : Fin p.T => downAtTimeLaw p)
    ((A : Set (Fin p.T)).pi (fun _ => {v | affineHash (v i) M = 1})) = _
  rw [Measure.pi_pi_finset]
  simp only [hone, Finset.prod_const]

theorem timesAfter_bank_eq (bank bank' : DownBank p) (side : Side p)
    (i : Fin (p.m - 1)) (start : Fin p.T) :
    timesAfter p ids rewards C_star C_h eta (coordinates p bank side) i start =
      timesAfter p ids rewards C_star C_h eta (coordinates p bank' side) i start :=
  congrArg (fun A => A.filter (fun t => start ≤ t))
    (eligibleTimes_bank_eq p ids rewards C_star C_h eta bank bank' side i)

theorem firstTimes_bank_eq (bank bank' : DownBank p) (side : Side p)
    (i : Fin (p.m - 1)) (start : Fin p.T) (q : ℕ) :
    firstTimes p ids rewards C_star C_h eta (coordinates p bank side) i start q =
      firstTimes p ids rewards C_star C_h eta (coordinates p bank' side) i start q :=
  congrArg (fun A : Finset (Fin p.T) => (A.sort (· ≤ ·)).take q)
    (timesAfter_bank_eq p ids rewards C_star C_h eta bank bank' side i start)

theorem downSample_coordinates (bank : DownBank p) (side : Side p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    downSample p (coordinates p bank side) t i = bank t i := by
  rw [downSample_eq_bank, coordinates_split]

/-- The exact bank-section probability of physical fixed-start survival.
The zero case includes no eligible tests and insufficient remaining tests.
This evaluates every side, including points in null side cells. -/
theorem fixedStartSurvival_section_probability (side : Side p)
    (i : Fin (p.m - 1)) (start : Fin p.T)
    (M : Word (AffineBatchDecoder.width p)) (q : ℕ) :
    downBankLaw p {bank | coordinates p bank side ∈
        fixedStartSurvival p ids rewards C_star C_h eta i start M q} =
      if q ≤ (timesAfter p ids rewards C_star C_h eta
          (coordinates p (zeroBank p) side) i start).card
      then ((1 : ℝ≥0∞) / 2) ^ q else 0 := by
  let e₀ := coordinates p (zeroBank p) side
  have ht (bank : DownBank p) := timesAfter_bank_eq p ids rewards C_star C_h eta
    bank (zeroBank p) side i start
  have hf (bank : DownBank p) := firstTimes_bank_eq p ids rewards C_star C_h eta
    bank (zeroBank p) side i start q
  by_cases hq : q ≤ (timesAfter p ids rewards C_star C_h eta e₀ i start).card
  · dsimp only [e₀] at hq
    rw [ite_eq_left hq]
    let A := (firstTimes p ids rewards C_star C_h eta e₀ i start q).toFinset
    have hA : A.card = q := by
      rw [List.toFinset_card_of_nodup (firstTimes_nodup p ids rewards C_star C_h eta
        e₀ i start q), firstTimes_length, min_eq_left hq]
    have heq : {bank | coordinates p bank side ∈
        fixedStartSurvival p ids rewards C_star C_h eta i start M q} =
        {bank | ∀ t ∈ A, affineHash (bank t i) M = 1} := by
      ext bank
      rw [Set.mem_ofPred, mem_fixedStartSurvival_iff, ht bank, hf bank]
      simp only [hq, true_and, downSample_coordinates, Set.mem_ofPred, A, List.mem_toFinset]
      rfl
    rw [heq]
    calc
      _ = ((1 : ℝ≥0∞) / 2) ^ A.card := bank_equations_probability p i A M
      _ = _ := congrArg (fun n => ((1 : ℝ≥0∞) / 2) ^ n) hA
  · dsimp only [e₀] at hq
    rw [ite_eq_right hq]
    have heq : {bank | coordinates p bank side ∈
        fixedStartSurvival p ids rewards C_star C_h eta i start M q} = ∅ := by
      ext bank
      rw [Set.mem_ofPred, mem_fixedStartSurvival_iff, ht bank]
      simp only [hq, false_and, Set.mem_empty_iff_false]
    rw [heq, measure_empty]

theorem fixedStartSurvival_section_le (side : Side p)
    (i : Fin (p.m - 1)) (start : Fin p.T)
    (M : Word (AffineBatchDecoder.width p)) (q : ℕ) :
    downBankLaw p {bank | coordinates p bank side ∈
        fixedStartSurvival p ids rewards C_star C_h eta i start M q} ≤
      (2 ^ q : ℝ≥0∞)⁻¹ := by
  rw [fixedStartSurvival_section_probability]
  split_ifs
  · simp only [one_div, ENNReal.inv_pow, le_refl]
  · exact zero_le

/-- Physical fixed-start survival on an arbitrary measurable side cell.
The cell can fix continuous slices, UP/forward coordinates, private arrays
and the original J scalar. No positive cell mass or conditional law is assumed. -/
theorem fixedStartSurvival_side_probability_le (S : Set (Side p)) (hS : MeasurableSet S)
    (i : Fin (p.m - 1)) (start : Fin p.T)
    (M : Word (AffineBatchDecoder.width p)) (q : ℕ) :
    GeneratedBootstrapRoundLaw.originalLaw p
      {e | (affineDownSplitEquiv p e).2 ∈ S ∧
        e ∈ fixedStartSurvival p ids rewards C_star C_h eta i start M q} ≤
      (2 ^ q : ℝ≥0∞)⁻¹ * sideLaw p S := by
  let A : Set (DownBank p × Side p) :=
    {z | z.2 ∈ S ∧ coordinates p z.1 z.2 ∈
      fixedStartSurvival p ids rewards C_star C_h eta i start M q}
  have hA : MeasurableSet A :=
    (measurable_snd hS).inter
      ((measurableSet_fixedStartSurvival p ids rewards C_star C_h eta i start M q).preimage
        (affineDownSplitEquiv p).symm.measurable)
  have heq : (affineDownSplitEquiv p) ⁻¹' A =
      {e | (affineDownSplitEquiv p e).2 ∈ S ∧
        e ∈ fixedStartSurvival p ids rewards C_star C_h eta i start M q} := by
    ext e
    change (_ ∧ (affineDownSplitEquiv p).symm (affineDownSplitEquiv p e) ∈ _) ↔ _
    rw [MeasurableEquiv.symm_apply_apply]
    rfl
  rw [← heq, (measurePreserving_affineDownSplitEquiv p).measure_preimage
    hA.nullMeasurableSet]
  change (downBankLaw p).prod (sideLaw p) A ≤ _
  rw [Measure.prod_apply_symm hA]
  calc
    _ ≤ ∫⁻ side, S.indicator (fun _ => (2 ^ q : ℝ≥0∞)⁻¹) side ∂sideLaw p := by
      apply lintegral_mono
      intro side
      by_cases hs : side ∈ S
      · simpa only [A, Set.preimage_ofPred_eq, hs, true_and, Set.indicator_of_mem hs] using
          fixedStartSurvival_section_le p ids rewards C_star C_h eta side i start M q
      · simp only [A, Set.preimage_ofPred_eq, hs, false_and, Set.ofPred_false,
          measure_empty, Set.indicator_of_notMem hs, le_refl]
    _ = _ := lintegral_indicator_const hS _

theorem fixedStartSurvival_probability_le (i : Fin (p.m - 1)) (start : Fin p.T)
    (M : Word (AffineBatchDecoder.width p)) (q : ℕ) :
    GeneratedBootstrapRoundLaw.originalLaw p
      (fixedStartSurvival p ids rewards C_star C_h eta i start M q) ≤
      (2 ^ q : ℝ≥0∞)⁻¹ := by
  simpa only [Set.mem_univ, true_and, Set.ofPred_mem_eq, measure_univ, mul_one] using
    fixedStartSurvival_side_probability_le p ids rewards C_star C_h eta
      Set.univ MeasurableSet.univ i start M q

/-- Finite union of physical quota-test survivals. Coverage of the separate
literal suppressed parser event is not built into this definition. -/
def quotaSurvivalEvent : Set (GeneratedBootstrapRoundLaw.Coordinates p) :=
  ⋃ i : Fin (p.m - 1), ⋃ start : Fin p.T,
    ⋃ M : Word (AffineBatchDecoder.width p),
      fixedStartSurvival p ids rewards C_star C_h eta i start M (AffineBatchDecoder.quota p)

theorem measurableSet_quotaSurvivalEvent :
    MeasurableSet (quotaSurvivalEvent p ids rewards C_star C_h eta) :=
  MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun start =>
    MeasurableSet.iUnion fun M =>
      measurableSet_fixedStartSurvival p ids rewards C_star C_h eta i start M _

/-- Only `m-1` receivers, `T` calendar starts and `2^width` words occur.
Random activation and launch introduce no additional counting factor. -/
theorem quotaSurvivalEvent_probability_le :
    GeneratedBootstrapRoundLaw.originalLaw p (quotaSurvivalEvent p ids rewards C_star C_h eta) ≤
      (p.m - 1 : ℕ) * (p.T : ℝ≥0∞) * 2 ^ AffineBatchDecoder.width p *
        (2 ^ AffineBatchDecoder.quota p : ℝ≥0∞)⁻¹ := by
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  let F := fun i start M =>
    fixedStartSurvival p ids rewards C_star C_h eta i start M (AffineBatchDecoder.quota p)
  calc
    _ ≤ ∑ i : Fin (p.m - 1), μ (⋃ start : Fin p.T, ⋃ M, F i start M) :=
      measure_iUnion_fintype_le μ _
    _ ≤ ∑ i : Fin (p.m - 1), ∑ start : Fin p.T, ∑ M : Word (AffineBatchDecoder.width p),
        (2 ^ AffineBatchDecoder.quota p : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      apply le_trans (measure_iUnion_fintype_le μ _)
      apply Finset.sum_le_sum
      intro start _
      apply le_trans (measure_iUnion_fintype_le μ _)
      exact Finset.sum_le_sum fun M _ =>
        fixedStartSurvival_probability_le p ids rewards C_star C_h eta i start M _
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Word,
        Fintype.card_fun, ZMod.card, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]

/-- The actual source quota's logarithm arithmetic. The displayed power
difference is a product with an inverse real power, never Nat subtraction. -/
theorem quota_union_factor_le :
    ((p.m - 1 : ℕ) : ℝ) * (p.T : ℝ) * 2 ^ AffineBatchDecoder.width p *
        (2 ^ AffineBatchDecoder.quota p : ℝ)⁻¹ ≤ 1 / (4 * (N p : ℝ) ^ 2) := by
  let L := Nat.clog 2 (4 * (p.m - 1) * p.T * (N p) ^ 2)
  have hm : 0 < p.m - 1 := by have h := p.two_le_m; omega
  have hc : 0 < ((p.m - 1 : ℕ) : ℝ) * (p.T : ℝ) :=
    mul_pos (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr (T_pos p))
  have hn : 0 < (N p : ℝ) := Nat.cast_pos.mpr (N_pos p)
  have hT : (p.T : ℝ) ≠ 0 := (Nat.cast_pos.mpr (T_pos p)).ne'
  have hpow : 0 < (2 : ℝ) ^ AffineBatchDecoder.width p := pow_pos (by norm_num) _
  have hlog : (4 : ℝ) * ((p.m - 1 : ℕ) : ℝ) * p.T * (N p : ℝ) ^ 2 ≤ (2 : ℝ) ^ L := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2)
      (4 * (p.m - 1) * p.T * (N p) ^ 2)
  have hden : 0 < (4 : ℝ) * ((p.m - 1 : ℕ) : ℝ) * p.T * (N p : ℝ) ^ 2 := by
    rw [mul_assoc (4 : ℝ)]
    exact mul_pos (mul_pos (by norm_num) hc) (sq_pos_of_pos hn)
  calc
    _ = (((p.m - 1 : ℕ) : ℝ) * p.T) / (2 : ℝ) ^ L := by
      rw [AffineBatchDecoder.quota, pow_add]
      change _ = _ / (2 : ℝ) ^ Nat.clog 2 (4 * (p.m - 1) * p.T * N p ^ 2)
      field_simp [hpow.ne']
    _ ≤ (((p.m - 1 : ℕ) : ℝ) * p.T) /
        (4 * ((p.m - 1 : ℕ) : ℝ) * p.T * (N p : ℝ) ^ 2) :=
      div_le_div_of_nonneg_left hc.le hden hlog
    _ = _ := by field_simp [hT]

theorem quotaSurvivalEvent_real_probability_le :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (quotaSurvivalEvent p ids rewards C_star C_h eta) ≤
      ((p.m - 1 : ℕ) : ℝ) * p.T * 2 ^ AffineBatchDecoder.width p *
        (2 ^ AffineBatchDecoder.quota p : ℝ)⁻¹ := by
  have ht : ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
      (2 ^ AffineBatchDecoder.quota p : ℝ≥0∞)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))
        (ENNReal.pow_ne_top (by norm_num)))
      (ENNReal.inv_ne_top.mpr (pow_ne_zero _ (by norm_num)))
  have h := ENNReal.toReal_mono ht
    (quotaSurvivalEvent_probability_le p ids rewards C_star C_h eta)
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_inv] using h

/-- Numerical consequence for the physical fixed-start union, without a
claim that the literal suppressed parser event has been covered. -/
theorem quotaSurvivalEvent_real_probability_le_quarter :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
      (quotaSurvivalEvent p ids rewards C_star C_h eta) ≤ 1 / (4 * (N p : ℝ) ^ 2) :=
  (quotaSurvivalEvent_real_probability_le p ids rewards C_star C_h eta).trans
    (quota_union_factor_le p)

end Bandits.Support.ReferenceSuppressedDownTail

end
