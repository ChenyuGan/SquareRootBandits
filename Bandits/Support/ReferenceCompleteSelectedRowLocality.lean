/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteRewardMeasurability
public import Bandits.Support.ReferenceInitializationIndexMixture
public import Bandits.Support.ReferenceActiveTemporalAssembly

/-!
# Complete reward locality on an original coordinator-index cell

For the same identification array, whole grid reward table, constants, and
complete private arrays, changing the coordinator scalar within one original
`J` cell leaves the generated initialization boundary and corrected launch
unchanged when the selected whole row is fixed. The physical suffix is compared
through its actual evidence projection, which erases only the unused
whole-row-indexed input retained by raw records. The resulting complete
received reward is pointwise invariant.

Sources: `sources/zip4/manuscript/07_public_setup.tex:123-164` and
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-75`.

These are internal deterministic producers. They do not establish a regret
bound, a probability estimate, or manuscript closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteSelectedRowLocality

open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceInitializationRun

variable
  (p : ReferenceCompletePhysicalRewards.Parameters)
  (rate : ReferenceCompletePhysicalRewards.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)
  (ids : IDArray p)
  (R S : CompleteRows p)
  (q : ReferenceInitializationIndexMixture.PrivateResidual p)
  (s t : ContinuousCategorical.Scalar)
  (j : Fin (ConstructorDimensions.M p))
  (hs : PrivateSourceStreams.coordinatorIndex p s = j)
  (ht : PrivateSourceStreams.coordinatorIndex p t = j)
  (hrow : R j = S j)

private theorem referenceInput_eq_fixedRowInput
    (p : ReferenceCompletePhysicalRewards.Parameters)
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (ids : IDArray p) (rows : CompleteRows p)
    (e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (ConstructorDimensions.M p))
    (hindex : PrivateSourceStreams.coordinatorIndex p e.1.2 = j) :
    ActualReferenceInitializationBlock.referenceInput
        ((ids, rows), e) rewards C_star C_h rate =
      ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h
        rate.eta (rows j) e := by
  unfold ActualReferenceInitializationBlock.referenceInput
    ReferenceInitializationIndexMixture.fixedRowInput
    ReferenceInitializationMeasurability.inputOfCoordinates
  simp only [ActualInitializationPhysicalStep.selectedRowIndex]
  rw [hindex]

private theorem records_totalReward_eq_evidenceRewardSum
    (p : ReferenceCompletePhysicalRewards.Parameters)
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    (records.map ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum =
    ((records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence).map
      (fun evidence : ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate) =>
        ∑ player : Fin p.m,
          ReferenceActivePhysicalHorizon.observationValue (evidence.ownEntries player).2)).sum := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      rfl

private theorem completeSuffixReward_eq_evidenceSum
    (p : ReferenceCompletePhysicalRewards.Parameters)
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h |>.map
      ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum =
    ((ReferenceCompletePhysicalHistory.completeSuffixEvidence rate source rewards C_star C_h).map
      (fun evidence : ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate) =>
        ∑ player : Fin p.m,
          ReferenceActivePhysicalHorizon.observationValue (evidence.ownEntries player).2)).sum := by
  unfold ReferenceCompletePhysicalHistory.completeSuffixEvidence
  exact records_totalReward_eq_evidenceRewardSum p rate
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)

private theorem activeState_eq_of_fields
    (p : ReferenceCompletePhysicalRewards.Parameters)
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (left right : ReferenceActivePhysicalStep.State p rate)
    (hcoord : left.coordinator = right.coordinator)
    (hbank : left.upDecoderBank = right.upDecoderBank)
    (hactivation : ∀ i, left.activations i = right.activations i)
    (hfollowers : ∀ i, left.followers i = right.followers i) : left = right := by
  cases left with
  | mk leftCoordinator leftBank leftActivations leftFollowers =>
      cases right with
      | mk rightCoordinator rightBank rightActivations rightFollowers =>
          have hcoord' : leftCoordinator = rightCoordinator := hcoord
          have hbank' : leftBank = rightBank := hbank
          have hactivation' : leftActivations = rightActivations := funext hactivation
          have hfoll' : leftFollowers = rightFollowers := funext hfollowers
          cases hcoord'
          cases hbank'
          cases hactivation'
          cases hfoll'
          rfl

include j hs ht hrow in
/-- The complete generated initialization boundary is fixed by the selected
whole row and all non-index private coordinates throughout one original J cell.
-/
theorem generatedBoundary_eq :
    ReferenceCompletePhysicalHistory.generatedBoundary rate
      ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q))
        rewards C_star C_h =
    ReferenceCompletePhysicalHistory.generatedBoundary rate
      ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q))
        rewards C_star C_h := by
  let eLeft := ReferenceInitializationIndexMixture.insertScalarResidual (s, q)
  let eRight := ReferenceInitializationIndexMixture.insertScalarResidual (t, q)
  have hinputLeft := referenceInput_eq_fixedRowInput p rate ids R eLeft rewards
    C_star C_h j (by simpa [eLeft, ReferenceInitializationIndexMixture.insertScalarResidual]
      using hs)
  have hinputRight := referenceInput_eq_fixedRowInput p rate ids S eRight rewards
    C_star C_h j (by simpa [eRight, ReferenceInitializationIndexMixture.insertScalarResidual]
      using ht)
  have houtput :
      ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput
            ((ids, R), eLeft) rewards C_star C_h rate) =
        ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput
            ((ids, S), eRight) rewards C_star C_h rate) := by
    calc
      _ = ReferenceInitializationRun.output
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h
            rate.eta (R j) eLeft) := congrArg ReferenceInitializationRun.output hinputLeft
      _ = ReferenceInitializationRun.output
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h
            rate.eta (R j) eRight) := by
              simpa [ReferenceInitializationIndexMixture.withCoordinatorScalar,
                eLeft, eRight, ReferenceInitializationIndexMixture.insertScalarResidual] using
                ReferenceInitializationIndexMixture.fixedRow_output_eq_of_coordinatorScalar_change
                  p ids rewards C_star C_h rate.eta (R j) eRight s
      _ = ReferenceInitializationRun.output
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h
            rate.eta (S j) eRight) := by rw [hrow]
      _ = _ := congrArg ReferenceInitializationRun.output hinputRight.symm
  calc
    _ = ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          ((ids, R), eLeft) rewards C_star C_h rate) := rfl
    _ = ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          ((ids, S), eRight) rewards C_star C_h rate) := houtput
    _ = _ := rfl

include j hs ht hrow in
/-- The actual corrected launch state, including its complete initial replay
and protocol memory, agrees for these two full sources. -/
theorem correctedLaunch_eq :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate
      ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q))
        rewards C_star C_h =
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate
      ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q))
        rewards C_star C_h := by
  let eLeft := ReferenceInitializationIndexMixture.insertScalarResidual (s, q)
  let eRight := ReferenceInitializationIndexMixture.insertScalarResidual (t, q)
  let sourceLeft : BootstrapPrivateRoundStreams.SourceInput p := ((ids, R), eLeft)
  let sourceRight : BootstrapPrivateRoundStreams.SourceInput p := ((ids, S), eRight)
  let inputLeft := ActualReferenceInitializationBlock.referenceInput
    sourceLeft rewards C_star C_h rate
  let inputRight := ActualReferenceInitializationBlock.referenceInput
    sourceRight rewards C_star C_h rate
  have hboundary : ReferenceInitializationRun.output inputLeft =
      ReferenceInitializationRun.output inputRight := by
    change ReferenceCompletePhysicalHistory.generatedBoundary rate sourceLeft rewards C_star C_h =
      ReferenceCompletePhysicalHistory.generatedBoundary rate sourceRight rewards C_star C_h
    exact generatedBoundary_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow
  have heta : inputLeft.eta = inputRight.eta := rfl
  have hrowInput : inputLeft.row = inputRight.row := by
    dsimp [inputLeft, inputRight, sourceLeft, sourceRight, eLeft, eRight,
      ActualReferenceInitializationBlock.referenceInput,
      ActualInitializationPhysicalStep.selectedRowIndex,
      ReferenceInitializationIndexMixture.insertScalarResidual]
    rw [hs, ht, hrow]
  have hordinary : ∀ i : Fin (p.m - 1),
      ReferenceInitializationRun.ordinary inputLeft (ReferenceInitializationRun.output inputLeft)
          (ActualReferenceInitializationBlock.refFollower i) =
        ReferenceInitializationRun.ordinary inputRight (ReferenceInitializationRun.output inputRight)
          (ActualReferenceInitializationBlock.refFollower i) := by
    intro i
    simp [ReferenceInitializationRun.ordinary, hboundary, hrowInput]
    rw [hboundary]
    cases heta
    rfl
  change ReferenceCorrectedInitializationLaunch.correctedLaunch rate sourceLeft rewards C_star C_h =
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate sourceRight rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate sourceLeft rewards C_star C_h with
  | none =>
      have hcrossLeft :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
          rate sourceLeft rewards C_star C_h).mp hlaunch
      have hcrossRight : (ReferenceInitializationRun.output inputRight).crossing = none := by
        rw [← hboundary]
        exact hcrossLeft
      have hlaunchRight :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
          rate sourceRight rewards C_star C_h).2 hcrossRight
      rw [hlaunchRight]
  | some payload =>
      have hsomeLeft : (ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate sourceLeft rewards C_star C_h).isSome = true := by
        rw [hlaunch]
        rfl
      have hcrossLeft :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate sourceLeft rewards C_star C_h).mp hsomeLeft
      have hcrossRight : (ReferenceInitializationRun.output inputRight).crossing.isSome = true := by
        rw [← hboundary]
        exact hcrossLeft
      obtain ⟨activeLeft, hpropLeft, _⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
          rate sourceLeft rewards C_star C_h hcrossLeft
      obtain ⟨activeRight, hpropRight, _⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
          rate sourceRight rewards C_star C_h hcrossRight
      rcases hpropLeft with ⟨hlaunchLeft, hcoordLeft, hbankLeft, hactivationLeft, hfollLeft⟩
      rcases hpropRight with ⟨hlaunchRight, hcoordRight, hbankRight, hactivationRight, hfollRight⟩
      have hactivation : ∀ i : Fin (p.m - 1), activeLeft.activations i = activeRight.activations i := by
        intro i
        have hoption := congrArg
          (fun boundary : ReferenceInitializationRun.Boundary p =>
            boundary.activation (ActualReferenceInitializationBlock.refFollower i)) hboundary
        exact Option.some.inj ((hactivationLeft i).trans (hoption.trans (hactivationRight i).symm))
      have hfollers : ∀ i : Fin (p.m - 1), activeLeft.followers i = activeRight.followers i := by
        intro i
        calc
          activeLeft.followers i = .ordinary
              (ReferenceInitializationRun.ordinary inputLeft (ReferenceInitializationRun.output inputLeft)
                (ActualReferenceInitializationBlock.refFollower i))
              (ActiveFollowerLifecycle.initialMemory p) := hfollLeft i
          _ = .ordinary
              (ReferenceInitializationRun.ordinary inputRight (ReferenceInitializationRun.output inputRight)
                (ActualReferenceInitializationBlock.refFollower i))
              (ActiveFollowerLifecycle.initialMemory p) := by rw [hordinary i]
          _ = activeRight.followers i := (hfollRight i).symm
      have hstate := activeState_eq_of_fields p rate activeLeft activeRight
        (hcoordLeft.trans hcoordRight.symm) (hbankLeft.trans hbankRight.symm)
        hactivation hfollers
      have hleftPayload : payload = activeLeft :=
        Option.some.inj (hlaunch.symm.trans hlaunchLeft)
      calc
        some payload = some activeLeft := congrArg some hleftPayload
        _ = some activeRight := congrArg some hstate
        _ = _ := hlaunchRight.symm

include j hs ht hrow in
/-- The full suffix evidence is pointwise invariant on the selected-row/J cell.
The comparison is of the evidence projection, not raw records retaining the
distinct whole row tables. -/
theorem completeSuffixEvidence_eq :
    ReferenceCompletePhysicalHistory.completeSuffixEvidence rate
      ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q))
        rewards C_star C_h =
    ReferenceCompletePhysicalHistory.completeSuffixEvidence rate
      ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q))
        rewards C_star C_h := by
  let eLeft := ReferenceInitializationIndexMixture.insertScalarResidual (s, q)
  let eRight := ReferenceInitializationIndexMixture.insertScalarResidual (t, q)
  let sourceLeft : BootstrapPrivateRoundStreams.SourceInput p := ((ids, R), eLeft)
  let sourceRight : BootstrapPrivateRoundStreams.SourceInput p := ((ids, S), eRight)
  have hselectedLeft : ActualInitializationPhysicalStep.selectedRowIndex p sourceLeft = j := by
    dsimp [sourceLeft, eLeft, ActualInitializationPhysicalStep.selectedRowIndex,
      ReferenceInitializationIndexMixture.insertScalarResidual]
    exact hs
  have hselectedRight : ActualInitializationPhysicalStep.selectedRowIndex p sourceRight = j := by
    dsimp [sourceRight, eRight, ActualInitializationPhysicalStep.selectedRowIndex,
      ReferenceInitializationIndexMixture.insertScalarResidual]
    exact ht
  have hboundary := generatedBoundary_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate sourceLeft rewards C_star C_h =
      ReferenceCompletePhysicalHistory.physicalStart rate sourceRight rewards C_star C_h := by
    change ReferenceInitializationRun.elapsed p
        (ReferenceCompletePhysicalHistory.generatedBoundary rate sourceLeft rewards C_star C_h).completed =
      ReferenceInitializationRun.elapsed p
        (ReferenceCompletePhysicalHistory.generatedBoundary rate sourceRight rewards C_star C_h).completed
    rw [hboundary]
  have hlaunchEq := correctedLaunch_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow
  change ReferenceCompletePhysicalHistory.completeSuffixEvidence rate sourceLeft rewards C_star C_h =
    ReferenceCompletePhysicalHistory.completeSuffixEvidence rate sourceRight rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate sourceLeft rewards C_star C_h with
  | none =>
      have hlaunchRight : ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate sourceRight rewards C_star C_h = none := by
        rw [← hlaunchEq]
        exact hlaunch
      simp [ReferenceCompletePhysicalHistory.completeSuffixEvidence,
        ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch, hlaunchRight]
  | some active =>
      have hlaunchRight : ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate sourceRight rewards C_star C_h = some active := by
        rw [← hlaunchEq]
        exact hlaunch
      let start := ReferenceCompletePhysicalHistory.physicalStart rate sourceLeft rewards C_star C_h
      let count := p.T - start
      have hspan : start + count ≤ p.T := by
        dsimp [count]
        have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate sourceLeft rewards C_star C_h
        omega
      have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate sourceLeft rewards C_star C_h active hlaunch
      have hcontrols : ∀ time : Fin p.T, start ≤ time.val → time.val < start + count →
          (R j).2 time = (S j).2 time := by
        intro time _ _
        rw [hrow]
      have hrewards : ∀ time : Fin p.T, start ≤ time.val → time.val < start + count →
          rewards time = rewards time := by
        intro time _ _
        rfl
      have hbefore : 0 < count → ∀ time : Fin p.T, time.val < start →
          ((R j).2 time).1 ContinuousControlSlice.Label.prop =
            ((S j).2 time).1 ContinuousControlSlice.Label.prop := by
        intro _ time _
        rw [hrow]
      have hrun := ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads
        active R S j rewards rewards start count hspan hmode hcontrols hrewards hbefore
      have hevidenceLeft := ReferenceCompletePhysicalHistory.completeSuffixEvidence_on_launch
        rate sourceLeft rewards C_star C_h active hlaunch
      have hevidenceRight := ReferenceCompletePhysicalHistory.completeSuffixEvidence_on_launch
        rate sourceRight rewards C_star C_h active hlaunchRight
      rw [hevidenceLeft, hevidenceRight]
      simpa [sourceLeft, sourceRight, hselectedLeft, hselectedRight, hstart, start, count] using
        hrun.2

include j hs ht hrow in
/-- The complete received reward through every physical round is invariant
under changing only the original coordinator scalar inside the same J cell. -/
theorem completeReward_eq :
    ReferenceCompletePhysicalRewards.completeReward rate
      ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q))
        rewards C_star C_h =
    ReferenceCompletePhysicalRewards.completeReward rate
      ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q))
        rewards C_star C_h := by
  let sourceLeft : BootstrapPrivateRoundStreams.SourceInput p :=
    ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q))
  let sourceRight : BootstrapPrivateRoundStreams.SourceInput p :=
    ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q))
  have hboundary := generatedBoundary_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow
  have hevidence := completeSuffixEvidence_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow
  have hsumLeft := completeSuffixReward_eq_evidenceSum p rate sourceLeft rewards C_star C_h
  have hsumRight := completeSuffixReward_eq_evidenceSum p rate sourceRight rewards C_star C_h
  have hsuffix :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate sourceLeft rewards C_star C_h |>.map
        ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate sourceRight rewards C_star C_h |>.map
        ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum := by
    calc
      _ = ((ReferenceCompletePhysicalHistory.completeSuffixEvidence rate sourceLeft rewards C_star C_h).map
          (fun evidence : ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate) =>
            ∑ player : Fin p.m,
              ReferenceActivePhysicalHorizon.observationValue (evidence.ownEntries player).2)).sum := hsumLeft
      _ = _ := by rw [hevidence]
      _ = _ := hsumRight.symm
  rw [ReferenceCompletePhysicalRewards.completeReward_calendar_split rate sourceLeft rewards C_star C_h,
    ReferenceCompletePhysicalRewards.completeReward_calendar_split rate sourceRight rewards C_star C_h]
  rw [hboundary, hsuffix]

end Bandits.Support.ReferenceCompleteSelectedRowLocality

end
