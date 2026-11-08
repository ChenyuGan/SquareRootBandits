/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownCurrentPair
public import Bandits.Support.ReferenceGeneratedPrelaunchDownActiveBridge
public import Bandits.Support.ReferenceGeneratedPrelaunchDownInactiveBridge
public import Bandits.Support.ReferenceGeneratedPrelaunchDownCohortStep

import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

/-!
# Fixed-birth prelaunch DOWN occurrence recurrence

This module counts actual prelaunch DOWN tests for one literal empty-bank
birth.  The occurrence event uses the existing predictable past indicator and
the existing current physical test.  The hashed event evaluates the original
selected-row affine pair.  Detector level zero is the actual birth readout;
positive levels are actual hashed occurrences.  No later launch state or
eventual decoder outcome is part of these definitions.

Sources: `appendix_a_local_protocol.tex:111-153`,
`appendix_b_communication.tex:724-736`, `07_public_setup.tex:60-112,127-164`,
and `05_binary_transport.tex:20-42` in `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownOccurrenceTail

open MeasureTheory ConstructorDimensions BootstrapDimensions
open ReferenceGeneratedPrelaunchDownPrefix
open ReferenceGeneratedPrelaunchDownCohort
open ReferenceGeneratedPrelaunchDownCurrentPair
open ReferenceSelectedAffinePairLaw GeneratedBootstrapRoundLaw
open scoped Classical ENNReal

variable {p : ConstructorDimensions.Parameters}

/-- One actual positive test whose preceding fixed-birth cohort has `q - 1`
pending tests, all carrying both required word flags. -/
def prelaunchDownOccurrence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : Fin p.T) : Prop :=
  source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k q hAlpha r w ∧
    A_r rate rewards C_star C_h z i r

/-- An occurrence whose original sample satisfies the retained affine
equation. -/
def prelaunchDownHashedOccurrence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : Fin p.T) : Prop :=
  prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r ∧
    AffineChannelLaw.affineHash
      (((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 r).2 (0, i)) w = 1

/-- The level-zero detector is exactly the actual empty-bank birth. -/
def prelaunchDownDetector
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    ℕ → Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  Nat.rec
    {z | birthAt rate rewards C_star C_h z i alpha hAlpha k}
    (fun q _ => {z | ∃ r : Fin p.T,
      prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q + 1)
        hAlpha w z r})

@[simp] theorem prelaunchDownDetector_zero
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w 0 =
      {z | birthAt rate rewards C_star C_h z i alpha hAlpha k} := rfl

@[simp] theorem prelaunchDownDetector_succ
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w (q + 1) =
      {z | ∃ r : Fin p.T,
        prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q + 1)
          hAlpha w z r} := rfl

def prelaunchPastRoundLabelRestrict
    (a r : Fin p.T) (har : a.val ≤ r.val)
    (label : PrivateRoundFreshness.PastRoundLabel p a) :
    PrivateRoundFreshness.PastRoundLabel p r :=
  ⟨⟨label.1.1, label.1.2.trans har⟩, lt_of_lt_of_le label.2 har⟩

/-- Restrict the actual strict-past coordinates at `r` to the earlier strict
past at `a`. The private base and target arrays are retained in full. -/
def prelaunchPastRestriction (a r : Fin p.T) (har : a.val ≤ r.val)
    (view : CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r) :
    CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a := by
  let privateView := view.2.2
  let calendarPast : CompleteRowStoppingLaw.PastArray p
      (GeneratedBootstrapRoundLaw.cutoff p a) := fun t =>
    view.2.1 ⟨t.1, by
      have hta : t.1.val < a.val := by
        simpa [GeneratedBootstrapRoundLaw.cutoff] using t.2
      exact lt_of_lt_of_le hta har⟩
  let scalarPast : PrivateRoundFreshness.PastRoundScalars p a := fun label =>
    privateView.2.1 (prelaunchPastRoundLabelRestrict a r har label)
  exact (view.1, (calendarPast, (privateView.1, (scalarPast, privateView.2.2))))

/-- Restriction recovers the original earlier-past view, coordinate by
coordinate, including the separate `J` scalar and all retained arrays. -/
theorem prelaunchPastRestriction_sourcePastView
    (a r : Fin p.T) (har : a.val ≤ r.val)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    prelaunchPastRestriction a r har
      (sourcePastView r z) = sourcePastView a z := by
  apply Prod.ext
  · simp [prelaunchPastRestriction, sourcePastView]
  · apply Prod.ext
    · funext t
      dsimp [sourcePastView, GeneratedBootstrapRoundLaw.past,
        GeneratedBootstrapRoundLaw.cutoff, prelaunchPastRestriction,
        CompleteRowStoppingLaw.calendarSplitEquiv,
        CompleteRowStoppingLaw.calendarizeRowEquiv,
        MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd]
      rfl
    · apply Prod.ext
      · simp [sourcePastView, GeneratedBootstrapRoundLaw.past,
          GeneratedBootstrapRoundLaw.cutoff, prelaunchPastRestriction,
          PrivateRoundFreshness.extendedPrivateRoundSplitEquiv,
          PrivateRoundFreshness.playerRoundScalarSplitEquiv,
          MeasurableEquiv.piEquivPiSubtypeProd,
          Equiv.piEquivPiSubtypeProd,
          MeasurableEquiv.prodAssoc, Equiv.prodAssoc,
          MeasurableEquiv.prodComm, Equiv.prodComm,
          MeasurableEquiv.prodCongr, Equiv.prodCongr_apply]
      · apply Prod.ext
        · funext label
          simp [sourcePastView, GeneratedBootstrapRoundLaw.past,
            GeneratedBootstrapRoundLaw.cutoff, prelaunchPastRestriction,
            prelaunchPastRoundLabelRestrict,
            PrivateRoundFreshness.extendedPrivateRoundSplitEquiv,
            PrivateRoundFreshness.playerRoundScalarSplitEquiv,
            MeasurableEquiv.piEquivPiSubtypeProd,
            Equiv.piEquivPiSubtypeProd,
            MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
            MeasurableEquiv.prodAssoc, Equiv.prodAssoc,
            MeasurableEquiv.prodComm, Equiv.prodComm,
            MeasurableEquiv.prodCongr, Equiv.prodCongr_apply]
        · simp [sourcePastView, GeneratedBootstrapRoundLaw.past,
            GeneratedBootstrapRoundLaw.cutoff, prelaunchPastRestriction,
            PrivateRoundFreshness.extendedPrivateRoundSplitEquiv,
            PrivateRoundFreshness.playerRoundScalarSplitEquiv,
            MeasurableEquiv.prodAssoc, Equiv.prodAssoc,
            MeasurableEquiv.prodComm, Equiv.prodComm,
            MeasurableEquiv.prodCongr, Equiv.prodCongr_apply]

/-- The literal strict-past restriction is measurable. It projects only the
earlier calendar labels and earlier round scalars, retaining all other factors. -/
theorem measurable_prelaunchPastRestriction (a r : Fin p.T) (har : a.val ≤ r.val) :
    Measurable (prelaunchPastRestriction (p := p) a r har) := by
  have hcalendar : Measurable (fun view : GeneratedBootstrapRoundLaw.Past p r =>
      fun t : CompleteRowStoppingLaw.PastIndex p (GeneratedBootstrapRoundLaw.cutoff p a) =>
        view.1 ⟨t.1, by
          have hta : t.1.val < a.val := by
            simpa [GeneratedBootstrapRoundLaw.cutoff] using t.2
          exact lt_of_lt_of_le hta har⟩) := by
    apply measurable_pi_iff.mpr
    intro t
    let idx : CompleteRowStoppingLaw.PastIndex p (GeneratedBootstrapRoundLaw.cutoff p r) :=
      ⟨t.1, by
      have hta : t.1.val < a.val := by
        simpa [GeneratedBootstrapRoundLaw.cutoff] using t.2
      exact lt_of_lt_of_le hta har⟩
    exact (measurable_pi_apply idx).comp measurable_fst
  have hround : Measurable (fun view : PrivateRoundFreshness.PastView p r =>
      fun label : PrivateRoundFreshness.PastRoundLabel p a =>
        view.2.1 (prelaunchPastRoundLabelRestrict a r har label)) := by
    apply measurable_pi_iff.mpr
    intro label
    exact (measurable_pi_apply
      (prelaunchPastRoundLabelRestrict a r har label)).comp
        (measurable_fst.comp measurable_snd)
  let restrictRounds := fun (view : PrivateRoundFreshness.PastView p r) =>
    fun label : PrivateRoundFreshness.PastRoundLabel p a =>
      view.2.1 (prelaunchPastRoundLabelRestrict a r har label)
  have hprivate : Measurable (fun view : PrivateRoundFreshness.PastView p r =>
      (view.1, (restrictRounds view, view.2.2))) :=
    measurable_fst.prodMk (hround.prodMk (measurable_snd.comp measurable_snd))
  have hcalendarFull : Measurable (fun view :
      CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r =>
      (fun past : GeneratedBootstrapRoundLaw.Past p r =>
        fun t : CompleteRowStoppingLaw.PastIndex p (GeneratedBootstrapRoundLaw.cutoff p a) =>
          past.1 ⟨t.1, by
            have hta : t.1.val < a.val := by
              simpa [GeneratedBootstrapRoundLaw.cutoff] using t.2
            exact lt_of_lt_of_le hta har⟩) view.2) :=
    hcalendar.comp measurable_snd
  have hprivateFull : Measurable (fun view :
      CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p r =>
      (view.2.2.1, (restrictRounds view.2.2, view.2.2.2.2))) := by
    simpa [Function.comp_def] using
      hprivate.comp (measurable_snd.comp measurable_snd)
  exact measurable_fst.prodMk (hcalendarFull.prodMk hprivateFull)

private theorem prefix_test_census_rank
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : Fin p.T) (active : ActiveProjection p i r.val
      (sourceReferenceInput rate rewards C_star C_h z).row (Nat.le_of_lt r.isLt)
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r))
    (hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r =
      .inl (.inl active)) :
    (source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r).length =
      AffineBatchDecoder.quota p * active.val.2.2.2.downBatch.completed.length +
        active.val.2.2.2.downBatch.pending.length := by
  classical
  have hcensus := source_prelaunch_down_prefix_census rate rewards C_star C_h z i r
  rw [hpref] at hcensus
  rcases hcensus with ⟨hmap, _, hcompleted, _⟩
  calc
    (source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r).length =
        ((source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r).map
          ReferenceGeneratedPrelaunchDownCohort.testEntry).length := by simp
    _ = (AffineBatchDecoder.collected
          (active.val.2.2.2.downBatch)).length := by rw [hmap]
    _ = active.val.2.2.2.downBatch.completed.length * AffineBatchDecoder.quota p +
          active.val.2.2.2.downBatch.pending.length :=
      AffineBatchDecoder.length_collected _ hcompleted
    _ = AffineBatchDecoder.quota p * active.val.2.2.2.downBatch.completed.length +
          active.val.2.2.2.downBatch.pending.length := by rw [Nat.mul_comm]

private theorem prefix_tests_successor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : Fin p.T) (hnext : r.val + 1 < p.T) :
    let rn : Fin p.T := ⟨r.val + 1, hnext⟩
    source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rn =
      source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++
        (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList := by
  classical
  dsimp only
  let rn : Fin p.T := ⟨r.val + 1, hnext⟩
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          have hstep :=
            ReferenceGeneratedPrelaunchDownActiveBridge.source_prelaunch_down_active_successor
              rate rewards C_star C_h z i r hnext
          rw [hpref] at hstep
          change source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rn =
            source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++
              (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList
          simpa [rn] using hstep.2.2.2.1
      | inr inactive =>
          have hstep :=
            ReferenceGeneratedPrelaunchDownInactiveBridge.source_prelaunch_down_inactive_successor
              rate rewards C_star C_h z i r hnext
          rw [hpref] at hstep
          rcases hstep with ⟨hcurrent, htests, hnext⟩
          cases hnextPrefix : source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
          | inl nextBranch =>
              cases nextBranch with
              | inl nextActive =>
                  rw [hnextPrefix] at hnext
                  have htestsNext := hnext.1
                  change source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rn = _
                  simpa [hcurrent, htests] using htestsNext
              | inr nextInactive =>
                  rw [hnextPrefix] at hnext
                  have htestsNext := hnext.1
                  change source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rn = _
                  simpa [hcurrent, htests] using htestsNext
          | inr nextStopped =>
              rw [hnextPrefix] at hnext
              have htestsNext := hnext.1
              change source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rn = _
              simpa [hcurrent, htests] using htestsNext
  | inr stopped =>
      have hstop :=
        ReferenceGeneratedPrelaunchDownInactiveBridge.source_prelaunch_down_stopped_to_terminal
          rate rewards C_star C_h z i r
      rw [hpref] at hstop
      rcases hstop with ⟨_, _, _, hcurrent, hfuture⟩
      obtain ⟨nextStopped, hnextPrefix, _, htests, _, _⟩ :=
        hfuture rn (by dsimp [rn]; omega)
      change source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rn = _
      simpa [hcurrent] using htests

private theorem prefix_tests_extend
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : Fin p.T) :
    ∀ n (hn : r.val + n < p.T),
      ∃ tail : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p),
        source_prelaunch_down_prefix_tests rate rewards C_star C_h z i
          (⟨r.val + n, hn⟩ : Fin p.T) =
            source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++ tail := by
  classical
  intro n
  induction n with
  | zero =>
      intro hn
      refine ⟨[], ?_⟩
      simp
  | succ n ih =>
      intro hn
      have hn' : r.val + n < p.T := by omega
      obtain ⟨tail, htail⟩ := ih hn'
      let rn : Fin p.T := ⟨r.val + n, hn'⟩
      have hnext : rn.val + 1 < p.T := by dsimp [rn]; omega
      have hstep0 := prefix_tests_successor rate rewards C_star C_h i z rn hnext
      let rnext : Fin p.T := ⟨rn.val + 1, hnext⟩
      have hstep : source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rnext =
          source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rn ++
            (source_prelaunch_down_current_test rate rewards C_star C_h z i rn).toList := by
        exact hstep0
      have hnextFin : rnext = (⟨r.val + (n + 1), hn⟩ : Fin p.T) := by
        apply Fin.ext
        dsimp [rnext, rn]
        omega
      refine ⟨tail ++ (source_prelaunch_down_current_test rate rewards C_star C_h z i rn).toList, ?_⟩
      rw [← hnextFin, hstep, htail, List.append_assoc]

private theorem prefix_tests_extend_of_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r s : Fin p.T) (hrs : r.val ≤ s.val) :
    ∃ tail : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p),
      source_prelaunch_down_prefix_tests rate rewards C_star C_h z i s =
        source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++ tail := by
  have hbound : r.val + (s.val - r.val) < p.T := by omega
  obtain ⟨tail, htail⟩ := prefix_tests_extend rate rewards C_star C_h i z r
    (s.val - r.val) hbound
  have hfin : (⟨r.val + (s.val - r.val), hbound⟩ : Fin p.T) = s := by
    apply Fin.ext
    change r.val + (s.val - r.val) = s.val
    calc
      r.val + (s.val - r.val) = (s.val - r.val) + r.val := Nat.add_comm _ _
      _ = s.val := Nat.sub_add_cancel hrs
  exact ⟨tail, hfin ▸ htail⟩

private theorem occurrence_rank
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : Fin p.T)
    (hOcc : prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r) :
    (source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r).length =
      AffineBatchDecoder.quota p * k + (q - 1) := by
  classical
  rcases hOcc with ⟨hI, _⟩
  have hI' := hI
  simp only [source_prelaunch_down_past_indicator] at hI'
  rcases hI' with ⟨_, _, _, _, hmatch⟩
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          simp only [hpref] at hmatch
          rcases hmatch with ⟨hk, _, hpending, _⟩
          have hcensus := prefix_test_census_rank rate rewards C_star C_h i z r
            active hpref
          rw [hk, hpending] at hcensus
          exact hcensus
      | inr inactive =>
          simp only [hpref] at hmatch
  | inr stopped =>
      simp only [hpref] at hmatch

private theorem prefix_tests_length_strict_of_current_positive
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r s : Fin p.T) (hrs : r.val < s.val)
    (hA : A_r rate rewards C_star C_h z i r) :
    (source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r).length <
      (source_prelaunch_down_prefix_tests rate rewards C_star C_h z i s).length := by
  classical
  let rn : Fin p.T := ⟨r.val + 1, by omega⟩
  have hnext : r.val + 1 < p.T := by omega
  cases htest : source_prelaunch_down_current_test rate rewards C_star C_h z i r with
  | none =>
      simp [A_r, htest] at hA
  | some test =>
      have hstep : source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rn =
          source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++ [test] := by
        have h := prefix_tests_successor rate rewards C_star C_h i z r hnext
        simpa [rn, htest] using h
      obtain ⟨tail, htail⟩ := prefix_tests_extend_of_le rate rewards C_star C_h i z rn s (by
        dsimp [rn]
        omega)
      rw [hstep] at htail
      have hlen := congrArg List.length htail
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega

/-- The same fixed-birth ordinal and pending length identify one actual
positive test time. -/
theorem prelaunch_occurrence_unique
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r r' : Fin p.T)
    (hOcc : prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r)
    (hOcc' : prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r') :
    r = r' := by
  by_contra hne
  have hvalNe : r.val ≠ r'.val := by
    intro hval
    exact hne (Fin.ext hval)
  change source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k q hAlpha r w ∧
      A_r rate rewards C_star C_h z i r at hOcc
  change source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k q hAlpha r' w ∧
      A_r rate rewards C_star C_h z i r' at hOcc'
  rcases lt_or_gt_of_ne hvalNe with hlt | hlt
  · have hA := hOcc.2
    have hstrict := prefix_tests_length_strict_of_current_positive rate rewards C_star C_h i z
      r r' hlt hA
    have hlen := occurrence_rank rate rewards C_star C_h i alpha k q hAlpha w z r hOcc
    have hlen' := occurrence_rank rate rewards C_star C_h i alpha k q hAlpha w z r' hOcc'
    rw [hlen, hlen'] at hstrict
    exact (Nat.lt_irrefl _ hstrict)
  · have hA := hOcc'.2
    have hstrict := prefix_tests_length_strict_of_current_positive rate rewards C_star C_h i z
      r' r hlt hA
    have hlen' := occurrence_rank rate rewards C_star C_h i alpha k q hAlpha w z r' hOcc'
    have hlen := occurrence_rank rate rewards C_star C_h i alpha k q hAlpha w z r hOcc
    rw [hlen', hlen] at hstrict
    exact (Nat.lt_irrefl _ hstrict)

/-- The predictable and current-positive factors are measurable in the original
source input. -/
theorem measurableSet_prelaunchDownOccurrence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (r : Fin p.T) :
    MeasurableSet {z | prelaunchDownOccurrence rate rewards C_star C_h i alpha k q
      hAlpha w z r} := by
  change MeasurableSet {z | source_prelaunch_down_past_indicator rate rewards C_star C_h
    z i alpha k q hAlpha r w ∧ A_r rate rewards C_star C_h z i r}
  exact (ReferenceGeneratedPrelaunchDownPastFactor.measurableSet_source_prelaunch_down_past_indicator
    rate rewards C_star C_h i alpha k q hAlpha r w).inter
      (measurableSet_A_r rate rewards C_star C_h i r)

/-- Each positive detector level has at most one actual test time, so its
indicator is exactly the finite sum of the time-indexed hashed indicators. -/
theorem prelaunch_occurrence_indicator_sum
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hq : 1 ≤ q) :
    (∑ r : Fin p.T,
      if prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k q
        hAlpha w z r then 1 else 0) =
      if z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w q
        then 1 else 0 := by
  classical
  cases q with
  | zero => omega
  | succ q0 =>
      have hunique : ∀ r ∈ Finset.univ.filter (fun r : Fin p.T =>
          prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q0 + 1)
            hAlpha w z r),
          ∀ s ∈ Finset.univ.filter (fun s : Fin p.T =>
            prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q0 + 1)
              hAlpha w z s), r = s := by
        intro r hr s hs
        have hrHit := (Finset.mem_filter.mp hr).2
        have hsHit := (Finset.mem_filter.mp hs).2
        apply prelaunch_occurrence_unique rate rewards C_star C_h i alpha k (q0 + 1)
          hAlpha w z r s hrHit.1 hsHit.1
      have hsum :
          (∑ r : Fin p.T,
            if prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q0 + 1)
              hAlpha w z r then 1 else 0) =
          (Finset.univ.filter (fun r : Fin p.T =>
            prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q0 + 1)
              hAlpha w z r)).card := by
        simpa using (Finset.sum_boole (fun r : Fin p.T =>
          prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q0 + 1)
            hAlpha w z r) Finset.univ)
      rw [hsum]
      by_cases hex : ∃ r : Fin p.T,
          prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q0 + 1)
            hAlpha w z r
      · obtain ⟨r0, hr0⟩ := hex
        have hfilter : Finset.univ.filter (fun r : Fin p.T =>
            prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q0 + 1)
              hAlpha w z r) = {r0} := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hr
            exact hunique r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩)
              r0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr0⟩)
          · intro heq
            subst r
            exact hr0
        rw [hfilter]
        simp only [Finset.card_singleton]
        have hdet : z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k
            hAlpha w (q0 + 1) := by
          rw [prelaunchDownDetector_succ]
          exact ⟨r0, hr0⟩
        rw [if_pos hdet]
      · have hfilter : Finset.univ.filter (fun r : Fin p.T =>
            prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q0 + 1)
              hAlpha w z r) = ∅ := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hr
            exact (hex ⟨r, hr⟩).elim
          · intro hr
            exact (Finset.notMem_empty r hr).elim
        rw [hfilter]
        have hdet : z ∉ prelaunchDownDetector rate rewards C_star C_h i alpha k
            hAlpha w (q0 + 1) := by
          rw [prelaunchDownDetector_succ]
          simpa using hex
        rw [Finset.card_empty, if_neg hdet]

/-- At the first positive level, the preceding detector is exactly the actual
empty-bank birth already required by the literal predictable indicator. -/
theorem prelaunch_occurrence_previous_one
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (alpha k : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : Fin p.T)
    (hOcc : prelaunchDownOccurrence rate rewards C_star C_h i alpha k 1
      hAlpha w z r) :
    z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w 0 := by
  change source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k 1
      hAlpha r w ∧ A_r rate rewards C_star C_h z i r at hOcc
  change z ∈ {z | birthAt rate rewards C_star C_h z i alpha hAlpha k}
  simp only [prelaunchDownDetector_zero, Set.mem_setOf_eq]
  have hIndicator := hOcc.1
  simp only [source_prelaunch_down_past_indicator] at hIndicator
  exact hIndicator.2.2.2.1

/-- A terminal birth has no positive-level occurrence, while its zero-level
birth mass remains represented by the terminal readout. -/
theorem prelaunchDownOccurrence_false_at_terminal_birth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (k q : ℕ)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : Fin p.T)
    (hAlpha : p.T ≤ r.val)
    (hOcc : prelaunchDownOccurrence rate rewards C_star C_h i p.T k q
      (Nat.le_refl p.T) w z r) : False := by
  change source_prelaunch_down_past_indicator rate rewards C_star C_h z i p.T k
      q (Nat.le_refl p.T) r w ∧ A_r rate rewards C_star C_h z i r at hOcc
  have hIndicator := hOcc.1
  simp only [source_prelaunch_down_past_indicator] at hIndicator
  omega

end Bandits.Support.ReferenceGeneratedPrelaunchDownOccurrenceTail

end
