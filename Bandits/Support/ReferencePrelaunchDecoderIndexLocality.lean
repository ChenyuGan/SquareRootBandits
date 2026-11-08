/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveInitialTransferCost
public import Bandits.Support.ReferenceCompleteSelectedRowLocality

/-!
# Original prelaunch decoder locality on a selected-row/J cell

The ordinary dated prelaunch DOWN failure bits and the original strict-past
decoder flag are fixed by the IDs, selected whole row and residual private
arrays while the coordinator scalar varies within the same original J cell.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferencePrelaunchDecoderIndexLocality

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceInitializationRun

private theorem referenceInput_eq_fixedRowInput
    (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (ids : IDArray p) (rows : CompleteRows p)
    (e : ExtendedPrivateCoordinates p)
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

private theorem prefixHistory_eq_of_boundary_and_physical
    (p : ConstructorDimensions.Parameters)
    (x y : ReferenceInitializationRun.Input p)
    (b b' : ReferenceInitializationRun.Boundary p)
    (hb : b = b')
    (h : b.completed < BootstrapDimensions.n_boot p)
    (h' : b'.completed < BootstrapDimensions.n_boot p)
    (n : ℕ) (hbefore : n ≤ ReferenceInitializationRun.elapsed p (b.completed + 1))
    (hbefore' : n ≤ ReferenceInitializationRun.elapsed p (b'.completed + 1))
    (hphysical : ∀ (b : ReferenceInitializationRun.Boundary p)
      (h : b.completed < BootstrapDimensions.n_boot p),
      ReferenceInitializationRun.physical x b h =
        ReferenceInitializationRun.physical y b h)
    (player : Fin p.m) :
    ReferencePrelaunchLifecycleReplay.prefixHistory
        (ReferenceInitializationRun.extendedHistory x b h player) n hbefore =
      ReferencePrelaunchLifecycleReplay.prefixHistory
        (ReferenceInitializationRun.extendedHistory y b' h' player) n hbefore' := by
  cases hb
  have hh : h = h' := Subsingleton.elim _ _
  cases hh
  have hbound : hbefore = hbefore' := Subsingleton.elim _ _
  cases hbound
  change (fun u : Fin n => ReferenceInitializationRun.extendedHistory x b h player
      (Fin.castLE hbefore u)) =
    (fun u : Fin n => ReferenceInitializationRun.extendedHistory y b h player
      (Fin.castLE hbefore u))
  funext u
  unfold ReferenceInitializationRun.extendedHistory
  split_ifs with hpast
  · rfl
  · exact congrArg (fun v => ReferenceInitializationRun.ownEntry v player
      ⟨(Fin.castLE hbefore u).val, Nat.lt_of_lt_of_le
        (Fin.castLE hbefore u).isLt
        (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))⟩)
      (hphysical b h)

private theorem ownEntry_eq_of_boundary_and_physical
    (p : ConstructorDimensions.Parameters)
    (x y : ReferenceInitializationRun.Input p)
    (b b' : ReferenceInitializationRun.Boundary p)
    (hb : b = b')
    (h : b.completed < BootstrapDimensions.n_boot p)
    (h' : b'.completed < BootstrapDimensions.n_boot p)
    (hphysical : ∀ (b : ReferenceInitializationRun.Boundary p)
      (h : b.completed < BootstrapDimensions.n_boot p),
      ReferenceInitializationRun.physical x b h =
        ReferenceInitializationRun.physical y b h)
    (player : Fin p.m) (r : Fin p.T) :
    ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical x b h)
        player r =
      ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical y b' h')
        player r := by
  cases hb
  have hh : h = h' := Subsingleton.elim _ _
  cases hh
  exact congrArg (fun v => ReferenceInitializationRun.ownEntry v player r)
    (hphysical b h)

private theorem prelaunchDownFailureAt_eq_of_run_physical
    (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z z' : SourceInput p)
    (hrow : (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
      rate rewards C_star C_h z).row =
        (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
          rate rewards C_star C_h z').row)
    (hrun : ∀ n,
      ReferenceInitializationRun.run
          (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
            rate rewards C_star C_h z) n =
        ReferenceInitializationRun.run
          (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
            rate rewards C_star C_h z') n)
    (hphysical : ∀ (b : ReferenceInitializationRun.Boundary p)
      (h : b.completed < BootstrapDimensions.n_boot p),
      ReferenceInitializationRun.physical
          (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
            rate rewards C_star C_h z) b h =
        ReferenceInitializationRun.physical
          (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
            rate rewards C_star C_h z') b h)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i r =
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z' i r := by
  classical
  let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h z
  let y := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h z'
  let s := BootstrapDimensions.roundBlockIndex p r
  have hrunS : ReferenceInitializationRun.run x s.val =
      ReferenceInitializationRun.run y s.val := hrun s.val
  change x.row = y.row at hrow
  change ∀ (b : ReferenceInitializationRun.Boundary p)
      (h : b.completed < BootstrapDimensions.n_boot p),
      ReferenceInitializationRun.physical x b h =
        ReferenceInitializationRun.physical y b h at hphysical
  unfold ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
  cases hL : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i r with
  | inl branchL =>
      cases branchL with
      | inl activeL =>
          cases hR : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
              rate rewards C_star C_h z' i r with
          | inl branchR =>
              cases branchR with
              | inl activeR =>
                  rcases activeL.property with ⟨hbeforeL, hactL, hstateL, hhistoryL⟩
                  rcases activeR.property with ⟨hbeforeR, hactR, hstateR, hhistoryR⟩
                  have hb : activeL.val.1.val = activeR.val.1.val :=
                    activeL.val.1.property.2.2.trans
                      (hrunS.trans activeR.val.1.property.2.2.symm)
                  have hactivation : activeL.val.2.1 = activeR.val.2.1 :=
                    Option.some.inj (by
                      calc
                        some activeL.val.2.1 = activeL.val.1.val.activation
                            (ActualReferenceInitializationBlock.refFollower i) := hactL.symm
                        _ = activeR.val.1.val.activation
                            (ActualReferenceInitializationBlock.refFollower i) :=
                              congrArg (fun b : ReferenceInitializationRun.Boundary p =>
                                b.activation (ActualReferenceInitializationBlock.refFollower i)) hb
                        _ = some activeR.val.2.1 := hactR)
                  have hhistory : activeL.val.2.2.1 = activeR.val.2.2.1 := by
                    calc
                      activeL.val.2.2.1 =
                          ReferencePrelaunchLifecycleReplay.prefixHistory
                            (ReferenceInitializationRun.extendedHistory x
                              activeL.val.1.val activeL.val.1.property.1
                              (PublicDiscreteDraws.followerPlayer p.two_le_m
                                (ActualReferenceInitializationBlock.refFollower i)))
                            r.val hbeforeL := hhistoryL
                      _ = ReferencePrelaunchLifecycleReplay.prefixHistory
                            (ReferenceInitializationRun.extendedHistory y
                              activeR.val.1.val activeR.val.1.property.1
                              (PublicDiscreteDraws.followerPlayer p.two_le_m
                                (ActualReferenceInitializationBlock.refFollower i)))
                            r.val hbeforeR :=
                          prefixHistory_eq_of_boundary_and_physical p x y
                            activeL.val.1.val activeR.val.1.val hb
                            activeL.val.1.property.1 activeR.val.1.property.1 r.val
                            hbeforeL hbeforeR hphysical
                            (PublicDiscreteDraws.followerPlayer p.two_le_m
                              (ActualReferenceInitializationBlock.refFollower i))
                      _ = activeR.val.2.2.1 := hhistoryR.symm
                  have hstate : activeL.val.2.2.2 = activeR.val.2.2.2 := by
                    have hstateL' : activeL.val.2.2.2 =
                        ReferencePrelaunchFollower.replay rate.eta i x.row
                          activeL.val.2.1 activeL.val.2.2.1
                          (Nat.le_of_lt r.isLt) := by
                      simpa [x, ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput,
                        ActualReferenceInitializationBlock.referenceInput] using hstateL
                    have hstateR' : activeR.val.2.2.2 =
                        ReferencePrelaunchFollower.replay rate.eta i y.row
                          activeR.val.2.1 activeR.val.2.2.1
                          (Nat.le_of_lt r.isLt) := by
                      simpa [y, ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput,
                        ActualReferenceInitializationBlock.referenceInput] using hstateR
                    have hrepRow :
                        ReferencePrelaunchFollower.replay rate.eta i x.row
                          activeL.val.2.1 activeL.val.2.2.1 (Nat.le_of_lt r.isLt) =
                        ReferencePrelaunchFollower.replay rate.eta i y.row
                          activeL.val.2.1 activeL.val.2.2.1 (Nat.le_of_lt r.isLt) := congrArg
                      (fun row : CompletePublicTable.CompleteRow p =>
                        ReferencePrelaunchFollower.replay rate.eta i row activeL.val.2.1
                          activeL.val.2.2.1 (Nat.le_of_lt r.isLt)) hrow
                    have hrepActivation :
                        ReferencePrelaunchFollower.replay rate.eta i y.row
                          activeL.val.2.1 activeL.val.2.2.1 (Nat.le_of_lt r.isLt) =
                        ReferencePrelaunchFollower.replay rate.eta i y.row
                          activeR.val.2.1 activeL.val.2.2.1 (Nat.le_of_lt r.isLt) := congrArg
                      (fun alpha : ReferencePrelaunchFollower.Activation p =>
                        ReferencePrelaunchFollower.replay rate.eta i y.row alpha
                          activeL.val.2.2.1 (Nat.le_of_lt r.isLt)) hactivation
                    have hrepHistory :
                        ReferencePrelaunchFollower.replay rate.eta i y.row
                          activeR.val.2.1 activeL.val.2.2.1 (Nat.le_of_lt r.isLt) =
                        ReferencePrelaunchFollower.replay rate.eta i y.row
                          activeR.val.2.1 activeR.val.2.2.1 (Nat.le_of_lt r.isLt) := congrArg
                      (fun history : ReferencePrelaunchFollower.LocalHistory p r.val =>
                        ReferencePrelaunchFollower.replay rate.eta i y.row activeR.val.2.1
                          history (Nat.le_of_lt r.isLt)) hhistory
                    have hrep :
                        ReferencePrelaunchFollower.replay rate.eta i x.row
                          activeL.val.2.1 activeL.val.2.2.1 (Nat.le_of_lt r.isLt) =
                        ReferencePrelaunchFollower.replay rate.eta i y.row
                          activeR.val.2.1 activeR.val.2.2.1 (Nat.le_of_lt r.isLt) :=
                      hrepRow.trans (hrepActivation.trans hrepHistory)
                    exact Eq.trans hstateL' (Eq.trans hrep hstateR'.symm)
                  have hown := ownEntry_eq_of_boundary_and_physical p x y
                    activeL.val.1.val activeR.val.1.val hb
                    activeL.val.1.property.1 activeR.val.1.property.1 hphysical
                    (PublicDiscreteDraws.followerPlayer p.two_le_m
                      (ActualReferenceInitializationBlock.refFollower i)) r
                  have htest :
                      (x.row, activeL.val.2.1,
                        ReferenceInitializationRun.ownEntry
                          (ReferenceInitializationRun.physical x
                            activeL.val.1.val activeL.val.1.property.1)
                          (PublicDiscreteDraws.followerPlayer p.two_le_m
                            (ActualReferenceInitializationBlock.refFollower i)) r,
                        activeL.val.2.2.2.downBatch) =
                        (y.row, activeR.val.2.1,
                          ReferenceInitializationRun.ownEntry
                            (ReferenceInitializationRun.physical y
                              activeR.val.1.val activeR.val.1.property.1)
                            (PublicDiscreteDraws.followerPlayer p.two_le_m
                              (ActualReferenceInitializationBlock.refFollower i)) r,
                          activeR.val.2.2.2.downBatch) := by
                    exact Prod.ext hrow (Prod.ext hactivation
                      (Prod.ext hown (congrArg (fun state => state.downBatch) hstate)))
                  have hdec :
                      decide (ReferencePrelaunchFollower.passing_at rate.eta i x.row
                        activeL.val.2.1 r
                        (ReferenceInitializationRun.ownEntry
                          (ReferenceInitializationRun.physical x
                            activeL.val.1.val activeL.val.1.property.1)
                          (PublicDiscreteDraws.followerPlayer p.two_le_m
                            (ActualReferenceInitializationBlock.refFollower i)) r)
                        activeL.val.2.2.2.downBatch) =
                      decide (ReferencePrelaunchFollower.passing_at rate.eta i y.row
                        activeR.val.2.1 r
                        (ReferenceInitializationRun.ownEntry
                          (ReferenceInitializationRun.physical y
                            activeR.val.1.val activeR.val.1.property.1)
                          (PublicDiscreteDraws.followerPlayer p.two_le_m
                            (ActualReferenceInitializationBlock.refFollower i)) r)
                        activeR.val.2.2.2.downBatch) := by
                    have hpass :
                        ReferencePrelaunchFollower.passing_at rate.eta i x.row
                          activeL.val.2.1 r
                          (ReferenceInitializationRun.ownEntry
                            (ReferenceInitializationRun.physical x
                              activeL.val.1.val activeL.val.1.property.1)
                            (PublicDiscreteDraws.followerPlayer p.two_le_m
                              (ActualReferenceInitializationBlock.refFollower i)) r)
                          activeL.val.2.2.2.downBatch =
                        ReferencePrelaunchFollower.passing_at rate.eta i y.row
                          activeR.val.2.1 r
                          (ReferenceInitializationRun.ownEntry
                            (ReferenceInitializationRun.physical y
                              activeR.val.1.val activeR.val.1.property.1)
                            (PublicDiscreteDraws.followerPlayer p.two_le_m
                              (ActualReferenceInitializationBlock.refFollower i)) r)
                          activeR.val.2.2.2.downBatch := by
                      exact congrArg
                        (fun args : CompletePublicTable.CompleteRow p ×
                            ReferencePrelaunchFollower.Activation p ×
                            (Fin p.K × ReferencePrelaunchFollower.Observation p) ×
                            AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) =>
                          ReferencePrelaunchFollower.passing_at rate.eta i args.1
                            args.2.1 r args.2.2.1 args.2.2.2) htest
                    apply Bool.eq_iff_iff.mpr
                    simp only [decide_eq_true_eq, hpass]
                  exact hdec
              | inr inactiveR =>
                  rcases activeL.property with ⟨_, hactL, _, _⟩
                  rcases inactiveR.property with ⟨_, hactR, _⟩
                  have hb : activeL.val.1.val = inactiveR.val.1.val :=
                    activeL.val.1.property.2.2.trans
                      (hrunS.trans inactiveR.val.1.property.2.2.symm)
                  have hsome : some activeL.val.2.1 = none := by
                    calc
                      some activeL.val.2.1 = activeL.val.1.val.activation
                          (ActualReferenceInitializationBlock.refFollower i) := hactL.symm
                      _ = inactiveR.val.1.val.activation
                          (ActualReferenceInitializationBlock.refFollower i) :=
                            congrArg (fun b : ReferenceInitializationRun.Boundary p =>
                              b.activation (ActualReferenceInitializationBlock.refFollower i)) hb
                      _ = none := hactR
                  cases hsome
          | inr stoppedR =>
              have hb : activeL.val.1.val = stoppedR.val.1 :=
                activeL.val.1.property.2.2.trans
                  (hrunS.trans stoppedR.property.2.1.symm)
              have hcross := congrArg ReferenceInitializationRun.Boundary.crossing hb
              exact False.elim (stoppedR.property.1
                        (hcross.symm.trans activeL.val.1.property.2.1))
      | inr inactiveL =>
          cases hR : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
              rate rewards C_star C_h z' i r with
          | inl branchR =>
              cases branchR with
              | inl activeR =>
                  rcases inactiveL.property with ⟨_, hactL, _⟩
                  rcases activeR.property with ⟨_, hactR, _, _⟩
                  have hb : inactiveL.val.1.val = activeR.val.1.val :=
                    inactiveL.val.1.property.2.2.trans
                      (hrunS.trans activeR.val.1.property.2.2.symm)
                  have hnone : none = some activeR.val.2.1 := by
                    calc
                      none = inactiveL.val.1.val.activation
                          (ActualReferenceInitializationBlock.refFollower i) := hactL.symm
                      _ = activeR.val.1.val.activation
                          (ActualReferenceInitializationBlock.refFollower i) :=
                            congrArg (fun b : ReferenceInitializationRun.Boundary p =>
                              b.activation (ActualReferenceInitializationBlock.refFollower i)) hb
                      _ = some activeR.val.2.1 := hactR
                  cases hnone
              | inr inactiveR =>
                  rcases inactiveL.property with ⟨hbeforeL, _, hhistoryL⟩
                  rcases inactiveR.property with ⟨hbeforeR, _, hhistoryR⟩
                  have hb : inactiveL.val.1.val = inactiveR.val.1.val :=
                    inactiveL.val.1.property.2.2.trans
                      (hrunS.trans inactiveR.val.1.property.2.2.symm)
                  have hhistory : inactiveL.val.2 = inactiveR.val.2 := by
                    calc
                      inactiveL.val.2 = ReferencePrelaunchLifecycleReplay.prefixHistory
                          (ReferenceInitializationRun.extendedHistory x
                            inactiveL.val.1.val inactiveL.val.1.property.1
                            (PublicDiscreteDraws.followerPlayer p.two_le_m
                              (ActualReferenceInitializationBlock.refFollower i)))
                          r.val hbeforeL := hhistoryL
                      _ = ReferencePrelaunchLifecycleReplay.prefixHistory
                          (ReferenceInitializationRun.extendedHistory y
                            inactiveR.val.1.val inactiveR.val.1.property.1
                            (PublicDiscreteDraws.followerPlayer p.two_le_m
                              (ActualReferenceInitializationBlock.refFollower i)))
                          r.val hbeforeR :=
                        prefixHistory_eq_of_boundary_and_physical p x y
                          inactiveL.val.1.val inactiveR.val.1.val hb
                          inactiveL.val.1.property.1 inactiveR.val.1.property.1 r.val
                          hbeforeL hbeforeR hphysical
                          (PublicDiscreteDraws.followerPlayer p.two_le_m
                            (ActualReferenceInitializationBlock.refFollower i))
                      _ = inactiveR.val.2 := hhistoryR.symm
                  rfl
          | inr stoppedR =>
              have hb : inactiveL.val.1.val = stoppedR.val.1 :=
                inactiveL.val.1.property.2.2.trans
                  (hrunS.trans stoppedR.property.2.1.symm)
              have hcross := congrArg ReferenceInitializationRun.Boundary.crossing hb
              exact False.elim (stoppedR.property.1
                (hcross.symm.trans inactiveL.val.1.property.2.1))
  | inr stoppedL =>
      cases hR : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i r with
      | inl branchR =>
          cases branchR with
          | inl activeR =>
              have hb : stoppedL.val.1 = activeR.val.1.val :=
                stoppedL.property.2.1.trans
                  (hrunS.trans activeR.val.1.property.2.2.symm)
              have hcross := congrArg ReferenceInitializationRun.Boundary.crossing hb
              exact False.elim (stoppedL.property.1
                (hcross.trans activeR.val.1.property.2.1))
          | inr inactiveR =>
              have hb : stoppedL.val.1 = inactiveR.val.1.val :=
                stoppedL.property.2.1.trans
                  (hrunS.trans inactiveR.val.1.property.2.2.symm)
              have hcross := congrArg ReferenceInitializationRun.Boundary.crossing hb
              exact False.elim (stoppedL.property.1
                (hcross.trans inactiveR.val.1.property.2.1))
      | inr stoppedR => rfl

private theorem prelaunchDownFailureAt_eq_of_generatedInput_eq
    (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z z' : SourceInput p)
    (hinput : ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h =
      ReferenceCompletePhysicalHistory.generatedInput rate z' rewards C_star C_h)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z i r =
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt
        rate rewards C_star C_h z' i r := by
  apply prelaunchDownFailureAt_eq_of_run_physical p rate rewards C_star C_h z z'
  · change (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h).row =
      (ReferenceCompletePhysicalHistory.generatedInput rate z' rewards C_star C_h).row
    exact congrArg ReferenceInitializationRun.Input.row hinput
  · intro n
    exact congrArg (fun x => ReferenceInitializationRun.run x n) hinput
  · intro b h
    exact congrArg (fun x => ReferenceInitializationRun.physical x b h) hinput

private theorem sourceInput_eq_fixedRowInput
    (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (ids : IDArray p) (rows : CompleteRows p)
    (e : ExtendedPrivateCoordinates p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (ConstructorDimensions.M p))
    (hindex : PrivateSourceStreams.coordinatorIndex p e.1.2 = j) :
    ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h
        ((ids, rows), e) =
      ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h
        rate.eta (rows j) e := by
  exact referenceInput_eq_fixedRowInput p rate ids rows e rewards C_star C_h j hindex

/-- Every dated ordinary prelaunch DOWN decoder failure bit is unchanged
when the complete selected row and residual private arrays are fixed and the
original coordinator scalar varies within the same J cell. -/
theorem prelaunchDownFailureAt_eq_of_selectedRow_and_J_cell
    (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (ids : IDArray p) (R S : CompleteRows p)
    (q : ReferenceInitializationIndexMixture.PrivateResidual p)
    (s t : ContinuousCategorical.Scalar)
    (j : Fin (ConstructorDimensions.M p))
    (hs : PrivateSourceStreams.coordinatorIndex p s = j)
    (ht : PrivateSourceStreams.coordinatorIndex p t = j)
    (hrow : R j = S j)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt rate rewards C_star C_h
        ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q)) i r =
      ReferencePrelaunchDownDecisionReadout.prelaunchDownFailureAt rate rewards C_star C_h
        ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q)) i r := by
  let eS := ReferenceInitializationIndexMixture.insertScalarResidual (s, q)
  let eT := ReferenceInitializationIndexMixture.insertScalarResidual (t, q)
  let zL : SourceInput p := ((ids, R), eS)
  let zM : SourceInput p := ((ids, S), eS)
  let zR : SourceInput p := ((ids, S), eT)
  have hindexL : PrivateSourceStreams.coordinatorIndex p eS.1.2 = j := by
    simpa [eS, ReferenceInitializationIndexMixture.insertScalarResidual] using hs
  have hindexM : PrivateSourceStreams.coordinatorIndex p eS.1.2 = j := hindexL
  have hindexR : PrivateSourceStreams.coordinatorIndex p eT.1.2 = j := by
    simpa [eT, ReferenceInitializationIndexMixture.insertScalarResidual] using ht
  have hgenRow := ReferenceCompletePhysicalHistory.generatedInput_and_launch_eq_of_source_data
    rate zL zM rewards C_star C_h j rfl rfl hindexL hrow
  have hleftMid : ReferenceCompletePhysicalHistory.generatedInput rate zL rewards C_star C_h =
      ReferenceCompletePhysicalHistory.generatedInput rate zM rewards C_star C_h := hgenRow.1
  have hfailLeftMid := prelaunchDownFailureAt_eq_of_generatedInput_eq p rate rewards C_star C_h
    zL zM hleftMid i r
  have hfixedM := sourceInput_eq_fixedRowInput p rate ids S eS rewards C_star C_h j hindexM
  have hfixedR := sourceInput_eq_fixedRowInput p rate ids S eT rewards C_star C_h j hindexR
  have hcoord : ReferenceInitializationIndexMixture.withCoordinatorScalar eT s = eS := by
    rfl
  have hrun : ∀ n,
      ReferenceInitializationRun.run
          (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h zM) n =
        ReferenceInitializationRun.run
          (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h zR) n := by
    intro n
    calc
      _ = ReferenceInitializationRun.run
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h
            rate.eta (S j) eS) n :=
              congrArg (fun x => ReferenceInitializationRun.run x n) hfixedM
      _ = ReferenceInitializationRun.run
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h
            rate.eta (S j) (ReferenceInitializationIndexMixture.withCoordinatorScalar eT s)) n := by
              rw [hcoord]
      _ = ReferenceInitializationRun.run
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h
            rate.eta (S j) eT) n :=
              ReferenceInitializationIndexMixture.fixedRow_run_eq_of_coordinatorScalar_change
                p ids rewards C_star C_h rate.eta (S j) eT s n
      _ = _ := congrArg (fun x => ReferenceInitializationRun.run x n) hfixedR.symm
  have hphysical : ∀ (b : ReferenceInitializationRun.Boundary p)
      (h : b.completed < BootstrapDimensions.n_boot p),
      ReferenceInitializationRun.physical
          (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h zM)
          b h =
        ReferenceInitializationRun.physical
          (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput rate rewards C_star C_h zR)
          b h := by
    intro b h
    calc
      _ = ReferenceInitializationRun.physical
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h
            rate.eta (S j) eS) b h :=
              congrArg (fun x => ReferenceInitializationRun.physical x b h) hfixedM
      _ = ReferenceInitializationRun.physical
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h
            rate.eta (S j) (ReferenceInitializationIndexMixture.withCoordinatorScalar eT s)) b h := by
              rw [hcoord]
      _ = ReferenceInitializationRun.physical
          (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h
            rate.eta (S j) eT) b h :=
              ReferenceInitializationCausality.physical_independent_of_latentJ
                (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h
                  rate.eta (S j) eT) b h s
      _ = _ := congrArg (fun x => ReferenceInitializationRun.physical x b h) hfixedR.symm
  have hrowMid : (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
      rate rewards C_star C_h zM).row =
        (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
          rate rewards C_star C_h zR).row := by
    exact congrArg ReferenceInitializationRun.Input.row hfixedM |>.trans
      (congrArg ReferenceInitializationRun.Input.row hfixedR).symm
  have hfailMidRight := prelaunchDownFailureAt_eq_of_run_physical p rate rewards C_star C_h
    zM zR hrowMid hrun hphysical i r
  exact hfailLeftMid.trans hfailMidRight

/-- The original strict-past prelaunch decoder flag is fixed on the same
selected-row/J cell for every horizon prefix, including zero and the terminal
boundary. -/
theorem prelaunchPastDecoderFlag_eq_of_selectedRow_and_J_cell
    (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (ids : IDArray p) (R S : CompleteRows p)
    (q : ReferenceInitializationIndexMixture.PrivateResidual p)
    (s t : ContinuousCategorical.Scalar)
    (j : Fin (ConstructorDimensions.M p))
    (hs : PrivateSourceStreams.coordinatorIndex p s = j)
    (ht : PrivateSourceStreams.coordinatorIndex p t = j)
    (hrow : R j = S j)
    (n : ℕ) (hn : n ≤ p.T) :
    ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag rate rewards C_star C_h
        ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q)) n hn =
      ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag rate rewards C_star C_h
        ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q)) n hn := by
  unfold ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨k, i, hk⟩
    have hbit := prelaunchDownFailureAt_eq_of_selectedRow_and_J_cell p rate rewards C_star C_h
      ids R S q s t j hs ht hrow i (Fin.castLE hn k)
    exact ⟨k, i, Eq.mp (congrArg (fun b : Bool => b = true) hbit) hk⟩
  · rintro ⟨k, i, hk⟩
    have hbit := prelaunchDownFailureAt_eq_of_selectedRow_and_J_cell p rate rewards C_star C_h
      ids R S q s t j hs ht hrow i (Fin.castLE hn k)
    exact ⟨k, i, Eq.mpr (congrArg (fun b : Bool => b = true) hbit) hk⟩

end Bandits.Support.ReferencePrelaunchDecoderIndexLocality

end
