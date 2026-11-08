/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon
public import Bandits.Support.LaunchAssignmentCoordinateSplit
public import Bandits.Support.LaunchAssignmentFibreCoupling
public import Bandits.Support.ActualInitializationLaunchState

/-!
# First-round physical assignment-fibre congruence

This module compares the actual first postlaunch physical round after changing
only the complete assignment vector in the selected coordinator row's current
time-control slice. The original whole table, selected row index, time, state,
rewards, non-assignment scalar slice, and affine samples are retained.

Sources: `sources/zip4/manuscript/06_interruptions.tex:41-61,363-397,410-423`,
`sources/zip4/manuscript/05_binary_transport.tex:62-80`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalStep

namespace Bandits.Support.ReferenceFirstAssignmentFibreStep

abbrev Parameters := ReferenceActivePhysicalHorizon.Parameters
abbrev RateInput := ReferenceActivePhysicalHorizon.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- Package a source scalar label together with its literal proof that it is
outside the assignment-labelled subtype. -/
def nonAssignmentLabelOf (label : ContinuousControlSlice.Label p.m p.K)
    (hlabel : ¬ ∃ i : Fin (p.K + 1),
      label = ContinuousControlSlice.Label.assign i) :
    LaunchAssignmentCoordinateSplit.NonAssignmentLabel p :=
  ⟨label, hlabel⟩

/-- The exact complete time-control slice obtained by replacing the full
assignment vector and retaining the original split remainder. -/
def assignmentCoordinateUpdate (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p) :
    ContinuousLearningRows.TimeControl p :=
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  e.symm (v, (e (x.row.2 x.time)).2)

/-- Replace only the coordinator's current time-control slice, leaving the
forward row, every other calendar slice, and the complete row carrier intact.
-/
def assignmentFibreRow (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p) : CompleteRow p :=
  (x.row.1, Function.update x.row.2 x.time (assignmentCoordinateUpdate x v))

/-- Replace only the selected complete row in the original whole public table.
All other rows, the selected index, state, time, active proof, and reward table
are inherited from `x`. -/
def assignmentFibreInput (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p) : RoundInput p rate :=
  { x with rows := Function.update x.rows x.selected (assignmentFibreRow x v) }

/-- The updated time-control slice has exactly the requested full `K+1`
assignment vector. The final orientation coordinate remains present. -/
theorem assignmentCoordinateUpdate_vector (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p) :
    ContinuousControlSlice.assignmentVector (assignmentCoordinateUpdate x v).1 = v := by
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  funext i
  have h := e.apply_symm_apply (v, (e (x.row.2 x.time)).2)
  change (e (e.symm (v, (e (x.row.2 x.time)).2))).1 i = v i
  exact congrArg (fun z => z.1 i) h

/-- Every non-assignment scalar in the selected current slice is retained by
the accepted inverse coordinate split. -/
theorem assignmentCoordinateUpdate_nonassignment (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (c : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :
    (assignmentCoordinateUpdate x v).1 c.1 = (x.row.2 x.time).1 c.1 := by
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  have h := congrArg (fun z => z.2.1 c) (e.apply_symm_apply
    (v, (e (x.row.2 x.time)).2))
  simpa [assignmentCoordinateUpdate, e,
    LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv,
    LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv,
    LaunchAssignmentCoordinateSplit.assignmentLabelEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.prodAssoc, Equiv.prodAssoc,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply] using h

/-- The accepted remainder, including every non-assignment scalar and all
affine samples, is unchanged. -/
theorem assignmentCoordinateUpdate_remainder (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p) :
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
      (assignmentCoordinateUpdate x v)).2 =
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
      (x.row.2 x.time)).2 := by
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  have h := congrArg Prod.snd (e.apply_symm_apply (v, (e (x.row.2 x.time)).2))
  simpa [assignmentCoordinateUpdate, e] using h

/-- The affine samples remain equal in the original `TimeControl` carrier.
-/
theorem assignmentCoordinateUpdate_affine (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p) :
    (assignmentCoordinateUpdate x v).2 = (x.row.2 x.time).2 := by
  change (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
      (assignmentCoordinateUpdate x v)).2.2 =
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
      (x.row.2 x.time)).2.2
  exact congrArg Prod.snd (assignmentCoordinateUpdate_remainder x v)

/-- Other calendar slices of the selected row are literally retained. -/
theorem assignmentFibreRow_other_time (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (t : Fin p.T) (ht : t ≠ x.time) :
    (assignmentFibreRow x v).2 t = x.row.2 t := by
  simp [assignmentFibreRow, ht]

/-- The current control slice is the literal inverse-split assignment update.
-/
theorem assignmentFibreRow_current_time (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p) :
    (assignmentFibreRow x v).2 x.time = assignmentCoordinateUpdate x v := by
  simp [assignmentFibreRow]

/-- The affine samples at the changed calendar coordinate remain the original
channel samples. -/
theorem assignmentFibreRow_affine_samples (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p) :
    ((assignmentFibreRow x v).2 x.time).2 = (x.row.2 x.time).2 := by
  rw [assignmentFibreRow_current_time]
  exact assignmentCoordinateUpdate_affine x v

/-- Every scalar outside the complete assignment-label subtype agrees at the
updated current coordinate. -/
theorem assignmentFibreRow_nonassignment_scalar (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p)
    (t : Fin p.T) :
    ((assignmentFibreRow x v).2 t).1 label.1 = (x.row.2 t).1 label.1 := by
  by_cases ht : t = x.time
  · subst t
    rw [assignmentFibreRow_current_time]
    exact assignmentCoordinateUpdate_nonassignment x v label
  · rw [assignmentFibreRow_other_time x v t ht]

/-- Two rows in the same updated input retain equal values at every
non-assignment scalar label. -/
theorem assignmentFibreRows_nonassignment_scalar (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :
    ((assignmentFibreRow x v).2 x.time).1 label.1 =
      ((assignmentFibreRow x w).2 x.time).1 label.1 := by
  rw [assignmentFibreRow_nonassignment_scalar x v label x.time,
    assignmentFibreRow_nonassignment_scalar x w label x.time]

/-- Two rows in the same updated input retain the original affine samples.
-/
theorem assignmentFibreRows_affine_samples (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p) :
    ((assignmentFibreRow x v).2 x.time).2 =
      ((assignmentFibreRow x w).2 x.time).2 := by
  rw [assignmentFibreRow_affine_samples x v,
    assignmentFibreRow_affine_samples x w]

/-- The first assignment's accepted local arm choice reads only source
non-assignment coordinates after its payload has been fixed. This covers the
live-fast, DATA-pilot, selected-DOWN, and tuple fallback branches. -/
theorem coordinatorArmChoice_assignmentFibre_eq (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (payload : AssignmentStartPayload.Input p rate.eta)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff x.time weights
        (assignmentFibreRow x v) =
      CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff x.time weights
        (assignmentFibreRow x w) := by
  let currentPending : Finset (ActiveRoundActions.Follower p.m) := by
    simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using pending
  change CoordinatorLocalArmChoice.coordinatorArmChoice payload currentPending cutoff x.time
      weights (assignmentFibreRow x v) =
    CoordinatorLocalArmChoice.coordinatorArmChoice payload currentPending cutoff x.time
      weights (assignmentFibreRow x w)
  rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core,
    CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core]
  let rowV := assignmentFibreRow x v
  let rowW := assignmentFibreRow x w
  let controlV := rowV.2 x.time
  let controlW := rowW.2 x.time
  have hslotScalar : controlV.1 ContinuousControlSlice.Label.slot =
      controlW.1 ContinuousControlSlice.Label.slot := by
    exact assignmentFibreRows_nonassignment_scalar x v w
      (nonAssignmentLabelOf _ (by
        simp [ContinuousControlSlice.Label.slot,
          ContinuousControlSlice.Label.assign]))
  have hfastScalar : controlV.1 ContinuousControlSlice.Label.fast =
      controlW.1 ContinuousControlSlice.Label.fast := by
    exact assignmentFibreRows_nonassignment_scalar x v w
      (nonAssignmentLabelOf _ (by
        simp [ContinuousControlSlice.Label.fast,
          ContinuousControlSlice.Label.assign]))
  have hselectedScalar : controlV.1 ContinuousControlSlice.Label.sel =
      controlW.1 ContinuousControlSlice.Label.sel := by
    exact assignmentFibreRows_nonassignment_scalar x v w
      (nonAssignmentLabelOf _ (by
        simp [ContinuousControlSlice.Label.sel,
          ContinuousControlSlice.Label.assign]))
  have hpilotScalar : controlV.1
      (ContinuousControlSlice.Label.pilot (ActiveRoundActions.coordinator p.two_le_m)) =
      controlW.1
      (ContinuousControlSlice.Label.pilot (ActiveRoundActions.coordinator p.two_le_m)) := by
    exact assignmentFibreRows_nonassignment_scalar x v w
      (nonAssignmentLabelOf _ (by
        simp [ContinuousControlSlice.Label.pilot,
          ContinuousControlSlice.Label.assign]))
  have hslot : PublicDiscreteDraws.slotDraw controlV.1 =
      PublicDiscreteDraws.slotDraw controlW.1 := by
    unfold PublicDiscreteDraws.slotDraw ContinuousControlSlice.coordinate
    rw [hslotScalar]
  have hselected : PublicDiscreteDraws.selectedFollowerDraw
      p.two_le_m p.m_lt_K controlV.1 =
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K controlW.1 := by
    unfold PublicDiscreteDraws.selectedFollowerDraw ContinuousControlSlice.coordinate
    rw [hselectedScalar]
  have hpilot : PublicDiscreteDraws.pilotDraw (K_pos p)
      (ActiveRoundActions.coordinator p.two_le_m) controlV.1 =
      PublicDiscreteDraws.pilotDraw (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) controlW.1 := by
    unfold PublicDiscreteDraws.pilotDraw ContinuousControlSlice.coordinate
    rw [hpilotScalar]
  have htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K controlV.1 =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K controlW.1 := by
    apply OrderedTupleSampler.sample_eq_of_tupleInputs_eq
    intro i
    exact assignmentFibreRows_nonassignment_scalar x v w
      (nonAssignmentLabelOf _ (by
        simp [ContinuousControlSlice.Label.tuple,
          ContinuousControlSlice.Label.assign]))
  have hdown (i : ActiveRoundActions.Follower p.m) :
      CoordinatorLocalArmChoice.currentDownHash payload controlV i =
        CoordinatorLocalArmChoice.currentDownHash payload controlW i := by
    change AffineChannelLaw.affineHash (controlV.2
          (CoordinatorLocalArmChoice.downChannel i))
        (CoordinatorLocalArmChoice.storedDownFlatWord payload i) =
      AffineChannelLaw.affineHash (controlW.2
          (CoordinatorLocalArmChoice.downChannel i))
        (CoordinatorLocalArmChoice.storedDownFlatWord payload i)
    rw [assignmentFibreRows_affine_samples x v w]
  unfold CoordinatorLocalArmChoice.coordinatorArmChoiceCore
  simp [rowV, rowW, controlV, controlW, hslot, hselected, hpilot, htuple,
    hfastScalar, hdown, CoordinatorLocalArmChoice.localFastDraw,
    ContinuousControlSlice.coordinate]

/-- The accepted local logging, DOWN, and UP branches read the same labelled
coordinates from both updated rows. The complete assignment vector may differ.
-/
theorem followerSelectedReads_assignmentFibre_agree (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (i : Fin (p.m - 1)) :
    ReferencePrelaunchFollower.selected_reads_agree i
      (assignmentFibreRow x v) (assignmentFibreRow x w) x.time := by
  have hscalar (label : ContinuousControlSlice.Label p.m p.K)
      (hlabel : ¬ ∃ j : Fin (p.K + 1),
        label = ContinuousControlSlice.Label.assign j) :
      ((assignmentFibreRow x v).2 x.time).1 label =
        ((assignmentFibreRow x w).2 x.time).1 label :=
    assignmentFibreRows_nonassignment_scalar x v w (nonAssignmentLabelOf label hlabel)
  have hthin : ((assignmentFibreRow x v).2 x.time).1 ContinuousControlSlice.Label.thin =
      ((assignmentFibreRow x w).2 x.time).1 ContinuousControlSlice.Label.thin :=
    hscalar ContinuousControlSlice.Label.thin (by
      intro h
      rcases h with ⟨j, hj⟩
      cases hj)
  have hpilot (j : Fin p.m) :
      ((assignmentFibreRow x v).2 x.time).1
          (ContinuousControlSlice.Label.pilot j) =
        ((assignmentFibreRow x w).2 x.time).1
          (ContinuousControlSlice.Label.pilot j) :=
    hscalar (ContinuousControlSlice.Label.pilot j) (by
      intro h
      rcases h with ⟨k, hk⟩
      cases hk)
  have hsample : ((assignmentFibreRow x v).2 x.time).2 (0, i) =
      ((assignmentFibreRow x w).2 x.time).2 (0, i) := by
    exact congrFun (assignmentFibreRows_affine_samples x v w) (0, i)
  refine ⟨hscalar ContinuousControlSlice.Label.slot (by
      intro h
      rcases h with ⟨j, hj⟩
      cases hj), ?_, ?_, ?_⟩
  · intro hdata
    refine ⟨?_, ?_⟩
    · exact hscalar ContinuousControlSlice.Label.rec (by
        intro h
        rcases h with ⟨j, hj⟩
        cases hj)
    · intro hsource
      refine ⟨hthin, ?_⟩
      intro j _hj
      exact hpilot j
  · intro _
    exact hscalar ContinuousControlSlice.Label.sel (by
      intro h
      rcases h with ⟨j, hj⟩
      cases hj)
  · intro _ _
    exact hsample

/-- The actual decoder-and-recovery diagnostic at an unoccupied follower is
preserved by the assignment fibre. Every runtime check, mismatch result,
cutoff scan, and recovered state remains in the compared output. -/
theorem referenceDownCut_assignmentFibre_eq (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (feedback : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    ReferenceDownReception.referenceDownCut p view i (assignmentFibreRow x v)
      x.time feedback rate state =
    ReferenceDownReception.referenceDownCut p view i (assignmentFibreRow x w)
      x.time feedback rate state := by
  classical
  let rowV := assignmentFibreRow x v
  let rowW := assignmentFibreRow x w
  have hscalar (label : ContinuousControlSlice.Label p.m p.K)
      (hlabel : ¬ ∃ j : Fin (p.K + 1),
        label = ContinuousControlSlice.Label.assign j) :
      (rowV.2 x.time).1 label = (rowW.2 x.time).1 label := by
    exact assignmentFibreRows_nonassignment_scalar x v w (nonAssignmentLabelOf label hlabel)
  have hslot : PublicDiscreteDraws.slotDraw (rowV.2 x.time).1 =
      PublicDiscreteDraws.slotDraw (rowW.2 x.time).1 := by
    have hslotScalar := hscalar ContinuousControlSlice.Label.slot (by
        intro h
        rcases h with ⟨j, hj⟩
        cases hj)
    unfold PublicDiscreteDraws.slotDraw ContinuousControlSlice.coordinate
    rw [hslotScalar]
  have hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (rowV.2 x.time).1 = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (rowW.2 x.time).1 := by
    have hselScalar : (rowV.2 x.time).1 ContinuousControlSlice.Label.sel =
        (rowW.2 x.time).1 ContinuousControlSlice.Label.sel := by
      exact hscalar ContinuousControlSlice.Label.sel (by
          intro h
          rcases h with ⟨j, hj⟩
          cases hj)
    unfold PublicDiscreteDraws.selectedFollowerDraw ContinuousControlSlice.coordinate
    rw [hselScalar]
  have hdown : ActiveFollowerDownAcceptance.downSelected p i rowV x.time =
      ActiveFollowerDownAcceptance.downSelected p i rowW x.time := by
    unfold ActiveFollowerDownAcceptance.downSelected
    rw [hslot, hselected]
  have hsample : (rowV.2 x.time).2 (0, i) = (rowW.2 x.time).2 (0, i) := by
    exact congrFun (assignmentFibreRows_affine_samples x v w) (0, i)
  have hinput : ActiveFollowerDownAcceptance.currentRoundInput p i rowV x.time
      feedback rate state = ActiveFollowerDownAcceptance.currentRoundInput p i rowW
      x.time feedback rate state := by
    cases hleft : ActiveFollowerDownAcceptance.currentRoundInput p i rowV x.time
        feedback rate state with
    | mk leftSelected leftReceiver leftSample leftReward =>
      cases hright : ActiveFollowerDownAcceptance.currentRoundInput p i rowW x.time
          feedback rate state with
      | mk rightSelected rightReceiver rightSample rightReward =>
        simp_all [ActiveFollowerDownAcceptance.currentRoundInput, hslot, hselected,
          hsample]
  have hdecode : ActiveFollowerDownAcceptance.currentDecodeStep p i rowV x.time
      feedback rate state = ActiveFollowerDownAcceptance.currentDecodeStep p i rowW
      x.time feedback rate state := by
    have htrace := congrArg (ActiveFollowerDownAcceptance.currentInputExtension p) hinput
    simpa [ActiveFollowerDownAcceptance.currentDecodeStep] using
      ActiveFollowerDownAcceptance.decodeStep_depends_on_current_input p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i rowV x.time feedback rate state))
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i rowW x.time feedback rate state))
        state.downBatch x.time (congrFun htrace x.time)
  have hprop (j : Fin p.T) :
      (CompletePublicTable.completeRowLearning p rowV j).1 ContinuousControlSlice.Label.prop =
        (CompletePublicTable.completeRowLearning p rowW j).1 ContinuousControlSlice.Label.prop := by
    by_cases hj : j = x.time
    · subst j
      change (rowV.2 x.time).1 ContinuousControlSlice.Label.prop =
        (rowW.2 x.time).1 ContinuousControlSlice.Label.prop
      exact hscalar ContinuousControlSlice.Label.prop (by
          intro h
          rcases h with ⟨k, hk⟩
          cases hk)
    · change (rowV.2 j).1 ContinuousControlSlice.Label.prop =
        (rowW.2 j).1 ContinuousControlSlice.Label.prop
      have hrowV : rowV.2 j = x.row.2 j := by
        simpa [rowV] using assignmentFibreRow_other_time x v j hj
      have hrowW : rowW.2 j = x.row.2 j := by
        simpa [rowW] using assignmentFibreRow_other_time x w j hj
      rw [hrowV, hrowW]
  have hscan (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) (hstart :
        (ActiveFollowerDownAcceptance.downStart p rate M).val ≤ x.time.val) :
      ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M x.time hstart rowV =
        ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M x.time hstart rowW := by
    unfold ActiveFollowerDownAcceptance.acceptedCutoffScan
    apply FollowerCutoffScan.completeRowCutoffScan_noninterference
    intro j _
    exact hprop j
  have hexpected : ReferenceDownReception.expectedDownFlatWord view i rowV x.time =
      ReferenceDownReception.expectedDownFlatWord view i rowW x.time := by
    cases view with
    | none => rfl
    | some selectedView =>
        have hchoice := coordinatorArmChoice_assignmentFibre_eq x v w
          selectedView.payload selectedView.pendingAtChoice selectedView.cutoff
          selectedView.complementWeights
        have hchoice' : CoordinatorLocalArmChoice.coordinatorArmChoice
            selectedView.payload selectedView.pendingAtChoice selectedView.cutoff x.time
              selectedView.complementWeights rowV =
            CoordinatorLocalArmChoice.coordinatorArmChoice selectedView.payload
              selectedView.pendingAtChoice selectedView.cutoff x.time
                selectedView.complementWeights rowW := by
          simpa [rowV, rowW] using hchoice
        have hbranch :
            ReferenceDownReception.selectedDownSenderBranch selectedView i rowV x.time =
              ReferenceDownReception.selectedDownSenderBranch selectedView i rowW x.time := by
          unfold ReferenceDownReception.selectedDownSenderBranch
          rw [hslot, hselected]
        have hcondition :
            (CoordinatorLocalArmChoice.coordinatorArmChoice selectedView.payload
              selectedView.pendingAtChoice selectedView.cutoff x.time
              selectedView.complementWeights rowV ≠ none ∧
              ReferenceDownReception.selectedDownSenderBranch selectedView i rowV x.time) ↔
            (CoordinatorLocalArmChoice.coordinatorArmChoice selectedView.payload
              selectedView.pendingAtChoice selectedView.cutoff x.time
              selectedView.complementWeights rowW ≠ none ∧
              ReferenceDownReception.selectedDownSenderBranch selectedView i rowW x.time) := by
          rw [hchoice', hbranch]
        by_cases hleft :
            CoordinatorLocalArmChoice.coordinatorArmChoice selectedView.payload
              selectedView.pendingAtChoice selectedView.cutoff x.time
              selectedView.complementWeights rowV ≠ none ∧
              ReferenceDownReception.selectedDownSenderBranch selectedView i rowV x.time
        · have hright := hcondition.mp hleft
          simp [ReferenceDownReception.expectedDownFlatWord, hleft, hright]
        · have hright : ¬ (CoordinatorLocalArmChoice.coordinatorArmChoice selectedView.payload
              selectedView.pendingAtChoice selectedView.cutoff x.time
              selectedView.complementWeights rowW ≠ none ∧
              ReferenceDownReception.selectedDownSenderBranch selectedView i rowW x.time) := by
            intro h
            exact hleft (hcondition.mpr h)
          simp [ReferenceDownReception.expectedDownFlatWord, hleft, hright]
  change ReferenceDownReception.referenceDownCut p view i rowV x.time feedback rate state =
    ReferenceDownReception.referenceDownCut p view i rowW x.time feedback rate state
  unfold ReferenceDownReception.referenceDownCut
  simp [hdown, hdecode, hexpected, hscan]

/-- A follower's prepared action reads only its literal local draws and its
UP affine sample; all five agree in these two updated complete rows. -/
theorem followerArmChoice_assignmentFibre_eq (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (i : Fin (p.m - 1))
    (offered : Option (OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) :
    ActiveFollowerArmChoice.followerArmChoice s (assignmentFibreRow x v) x.time i offered =
      ActiveFollowerArmChoice.followerArmChoice s (assignmentFibreRow x w) x.time i offered := by
  rw [ActiveFollowerArmChoice.followerArmChoice_eq_core,
    ActiveFollowerArmChoice.followerArmChoice_eq_core]
  let controlV := (assignmentFibreRow x v).2 x.time
  let controlW := (assignmentFibreRow x w).2 x.time
  have hslotScalar := assignmentFibreRows_nonassignment_scalar x v w
    (nonAssignmentLabelOf ContinuousControlSlice.Label.slot (by
      intro h
      rcases h with ⟨j, hj⟩
      cases hj))
  have hselectedScalar := assignmentFibreRows_nonassignment_scalar x v w
    (nonAssignmentLabelOf ContinuousControlSlice.Label.sel (by
      intro h
      rcases h with ⟨j, hj⟩
      cases hj))
  have htupleScalar (j : Fin p.m) := assignmentFibreRows_nonassignment_scalar x v w
    (nonAssignmentLabelOf (ContinuousControlSlice.Label.tuple j) (by
      intro h
      rcases h with ⟨r, hr⟩
      cases hr))
  have hpilotScalar := assignmentFibreRows_nonassignment_scalar x v w
    (nonAssignmentLabelOf (ContinuousControlSlice.Label.pilot
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) (by
      intro h
      rcases h with ⟨j, hj⟩
      cases hj))
  have hslot : PublicDiscreteDraws.slotDraw controlV.1 =
      PublicDiscreteDraws.slotDraw controlW.1 := by
    have hs : controlV.1 ContinuousControlSlice.Label.slot =
        controlW.1 ContinuousControlSlice.Label.slot := by
      simpa [controlV, controlW, nonAssignmentLabelOf] using hslotScalar
    unfold PublicDiscreteDraws.slotDraw ContinuousControlSlice.coordinate
    rw [hs]
  have hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K controlV.1 =
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K controlW.1 := by
    have hs : controlV.1 ContinuousControlSlice.Label.sel =
        controlW.1 ContinuousControlSlice.Label.sel := by
      simpa [controlV, controlW, nonAssignmentLabelOf] using hselectedScalar
    unfold PublicDiscreteDraws.selectedFollowerDraw ContinuousControlSlice.coordinate
    rw [hs]
  have htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K controlV.1 =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K controlW.1 := by
    apply OrderedTupleSampler.sample_eq_of_tupleInputs_eq
    intro j
    simpa [controlV, controlW, nonAssignmentLabelOf] using htupleScalar j
  have hpilot : PublicDiscreteDraws.pilotDraw (K_pos p)
      (PublicDiscreteDraws.followerPlayer p.two_le_m i) controlV.1 =
      PublicDiscreteDraws.pilotDraw (K_pos p)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) controlW.1 := by
    have hs : controlV.1 (ContinuousControlSlice.Label.pilot
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
        controlW.1 (ContinuousControlSlice.Label.pilot
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
      simpa [controlV, controlW, nonAssignmentLabelOf] using hpilotScalar
    unfold PublicDiscreteDraws.pilotDraw ContinuousControlSlice.coordinate
    rw [hs]
  have hsample : controlV.2 (1, i) = controlW.2 (1, i) := by
    exact congrFun (assignmentFibreRows_affine_samples x v w) (1, i)
  exact ActiveFollowerArmChoice.followerArmChoiceCore_eq_of_same_local_draws
    s controlV controlW i offered hslot hselected htuple hpilot hsample

/-- The checked follower UP offer uses the same slot and selected-follower
coordinates in the two rows; all state-domain and codec checks are preserved.
-/
theorem checkedUpOffer_assignmentFibre_eq (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
        (assignmentFibreRow x v) (x.state.activations i) x.time state =
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
        (assignmentFibreRow x w) (x.state.activations i) x.time state := by
  have hslotScalar := assignmentFibreRows_nonassignment_scalar x v w
    (nonAssignmentLabelOf ContinuousControlSlice.Label.slot (by
      intro h
      rcases h with ⟨j, hj⟩
      cases hj))
  have hselectedScalar := assignmentFibreRows_nonassignment_scalar x v w
    (nonAssignmentLabelOf ContinuousControlSlice.Label.sel (by
      intro h
      rcases h with ⟨j, hj⟩
      cases hj))
  have hslot : PublicDiscreteDraws.slotDraw
      ((assignmentFibreRow x v).2 x.time).1 = PublicDiscreteDraws.slotDraw
      ((assignmentFibreRow x w).2 x.time).1 := by
    have hs : ((assignmentFibreRow x v).2 x.time).1 ContinuousControlSlice.Label.slot =
        ((assignmentFibreRow x w).2 x.time).1 ContinuousControlSlice.Label.slot := by
      simpa [nonAssignmentLabelOf] using hslotScalar
    unfold PublicDiscreteDraws.slotDraw ContinuousControlSlice.coordinate
    rw [hs]
  have hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      ((assignmentFibreRow x v).2 x.time).1 = PublicDiscreteDraws.selectedFollowerDraw
      p.two_le_m p.m_lt_K ((assignmentFibreRow x w).2 x.time).1 := by
    have hs : ((assignmentFibreRow x v).2 x.time).1 ContinuousControlSlice.Label.sel =
        ((assignmentFibreRow x w).2 x.time).1 ContinuousControlSlice.Label.sel := by
      simpa [nonAssignmentLabelOf] using hselectedScalar
    unfold PublicDiscreteDraws.selectedFollowerDraw ContinuousControlSlice.coordinate
    rw [hs]
  have htest : ActiveFollowerQueueOperation.selectedUpRound i
      (assignmentFibreRow x v) (x.state.activations i) x.time =
    ActiveFollowerQueueOperation.selectedUpRound i
      (assignmentFibreRow x w) (x.state.activations i) x.time := by
    simp [ActiveFollowerQueueOperation.selectedUpRound, hslot, hselected]
  unfold ActiveFollowerQueueOperation.checkedUpOffer
  rw [htest]

/-- The actual first-choice preparation keeps each follower's choice state
and arm across the assignment fibre. The `PreparedRound` row fields remain
the respective original complete rows. -/
theorem followerPrepare_arm_configuration_eq (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (i : Fin (p.m - 1))
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    let preparedV := DeclaredFollowerLocalRound.prepare rate i
      (assignmentFibreRow x v) (x.state.activations i) x.time (x.active i) configuration
    let preparedW := DeclaredFollowerLocalRound.prepare rate i
      (assignmentFibreRow x w) (x.state.activations i) x.time (x.active i) configuration
    preparedV.arm = preparedW.arm ∧ preparedV.configuration = preparedW.configuration := by
  classical
  cases configuration with
  | dagger => simp [DeclaredFollowerLocalRound.prepare]
  | ordinary state memory =>
      dsimp only [DeclaredFollowerLocalRound.prepare]
      cases hstart : ActiveFollowerLifecycle.startRound rate.eta x.time state memory with
      | error failure => simp [DeclaredFollowerLocalRound.prepare, hstart]
      | ok pair =>
          obtain ⟨choiceState, choiceMemory⟩ := pair
          have hoff := checkedUpOffer_assignmentFibre_eq x v w i choiceState
          simp only [hoff]
          cases hoffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
              (assignmentFibreRow x w) (x.state.activations i) x.time choiceState with
          | failure => simp [hoffer]
          | noOffer =>
              have hchoice := followerArmChoice_assignmentFibre_eq x v w choiceState i none
              simp only [hchoice]
              cases hresult : ActiveFollowerArmChoice.followerArmChoice choiceState
                  (assignmentFibreRow x w) x.time i none <;>
                simp [hoffer, hresult]
          | offer offered =>
              have hchoice := followerArmChoice_assignmentFibre_eq x v w choiceState i
                (some offered)
              simp only [hchoice]
              cases hresult : ActiveFollowerArmChoice.followerArmChoice choiceState
                  (assignmentFibreRow x w) x.time i (some offered) <;>
                simp [hoffer, hresult]

/-- The first accepted slow-set sampler is the sole assignment dependence of
the installed payload. This retains the full input vectors in each launch. -/
theorem firstLaunchSlowSet_assignmentFibre_eq (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (hsampler : LaunchAssignmentFibreCoupling.firstLaunchSampler p v =
      LaunchAssignmentFibreCoupling.firstLaunchSampler p w) :
    FirstAssignmentLaunch.Input.slowSet
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput (assignmentFibreInput x v))) =
      FirstAssignmentLaunch.Input.slowSet
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput (assignmentFibreInput x w))) := by
  let launchV := CoordinatorRoundDispatch.firstLaunchInput
    (ReferenceActivePhysicalStep.firstInput (assignmentFibreInput x v))
  let launchW := CoordinatorRoundDispatch.firstLaunchInput
    (ReferenceActivePhysicalStep.firstInput (assignmentFibreInput x w))
  have hvectorV : LaterAssignmentStartOperation.ownAssignmentVector
      (assignmentFibreRow x v) x.time = v := by
    change ContinuousControlSlice.assignmentVector
      ((assignmentFibreRow x v).2 x.time).1 = v
    rw [assignmentFibreRow_current_time]
    exact assignmentCoordinateUpdate_vector x v
  have hvectorW : LaterAssignmentStartOperation.ownAssignmentVector
      (assignmentFibreRow x w) x.time = w := by
    change ContinuousControlSlice.assignmentVector
      ((assignmentFibreRow x w).2 x.time).1 = w
    rw [assignmentFibreRow_current_time]
    exact assignmentCoordinateUpdate_vector x w
  have hcoordinatesV : launchV.coordinates = v := by
    funext j
    simpa [launchV, CoordinatorRoundDispatch.firstLaunchInput,
      ReferenceActivePhysicalStep.firstInput, assignmentFibreInput,
      ReferenceActivePhysicalStep.RoundInput.row] using
      congrFun hvectorV j
  have hcoordinatesW : launchW.coordinates = w := by
    funext j
    simpa [launchW, CoordinatorRoundDispatch.firstLaunchInput,
      ReferenceActivePhysicalStep.firstInput, assignmentFibreInput,
      ReferenceActivePhysicalStep.RoundInput.row] using
      congrFun hvectorW j
  change FirstAssignmentLaunch.Input.slowSet launchV =
    FirstAssignmentLaunch.Input.slowSet launchW
  change LaunchAssignmentFibreCoupling.firstLaunchSampler p launchV.coordinates =
    LaunchAssignmentFibreCoupling.firstLaunchSampler p launchW.coordinates
  rw [hcoordinatesV, hcoordinatesW]
  exact hsampler

/-- The first launch record, payload, clock and zero seed depend on this
assignment input through its sampled slow set. The launch's retained full
coordinate vectors remain separate. -/
theorem firstPayload_assignmentFibre_eq (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (hsampler : LaunchAssignmentFibreCoupling.firstLaunchSampler p v =
      LaunchAssignmentFibreCoupling.firstLaunchSampler p w) :
    let launchV := CoordinatorRoundDispatch.firstLaunchInput
      (ReferenceActivePhysicalStep.firstInput (assignmentFibreInput x v))
    let launchW := CoordinatorRoundDispatch.firstLaunchInput
      (ReferenceActivePhysicalStep.firstInput (assignmentFibreInput x w))
    AssignmentStartPayload.Input.ofFirstAssignment launchV =
      AssignmentStartPayload.Input.ofFirstAssignment launchW := by
  let launchV : FirstAssignmentLaunch.Input p rate.eta :=
    CoordinatorRoundDispatch.firstLaunchInput
    (ReferenceActivePhysicalStep.firstInput (assignmentFibreInput x v))
  let launchW : FirstAssignmentLaunch.Input p rate.eta :=
    CoordinatorRoundDispatch.firstLaunchInput
    (ReferenceActivePhysicalStep.firstInput (assignmentFibreInput x w))
  have hslow : launchV.slowSet = launchW.slowSet := by
    simpa [launchV, launchW, CoordinatorRoundDispatch.firstLaunchInput,
      ReferenceActivePhysicalStep.firstInput, assignmentFibreInput,
      ReferenceActivePhysicalStep.RoundInput.row] using
      firstLaunchSlowSet_assignmentFibre_eq x v w hsampler
  change AssignmentStartPayload.Input.ofFirstAssignment launchV =
    AssignmentStartPayload.Input.ofFirstAssignment launchW
  simp only [AssignmentStartPayload.Input.ofFirstAssignment]
  rw [hslow]
  rfl

/-- The installed live registers agree after the common first sampler value;
the complete `FirstInstallation.start` itself is intentionally not equated,
because it retains the distinct assignment vectors. -/
theorem firstRegisters_assignmentFibre_eq (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (hsampler : LaunchAssignmentFibreCoupling.firstLaunchSampler p v =
      LaunchAssignmentFibreCoupling.firstLaunchSampler p w) :
    let launchV := CoordinatorRoundDispatch.firstLaunchInput
      (ReferenceActivePhysicalStep.firstInput (assignmentFibreInput x v))
    let launchW := CoordinatorRoundDispatch.firstLaunchInput
      (ReferenceActivePhysicalStep.firstInput (assignmentFibreInput x w))
    (CoordinatorAssignmentRegisterInstall.installFirst launchV).registers =
      (CoordinatorAssignmentRegisterInstall.installFirst launchW).registers := by
  let launchV : FirstAssignmentLaunch.Input p rate.eta :=
    CoordinatorRoundDispatch.firstLaunchInput
    (ReferenceActivePhysicalStep.firstInput (assignmentFibreInput x v))
  let launchW : FirstAssignmentLaunch.Input p rate.eta :=
    CoordinatorRoundDispatch.firstLaunchInput
    (ReferenceActivePhysicalStep.firstInput (assignmentFibreInput x w))
  have hslow : launchV.slowSet = launchW.slowSet := by
    simpa [launchV, launchW, CoordinatorRoundDispatch.firstLaunchInput,
      ReferenceActivePhysicalStep.firstInput, assignmentFibreInput,
      ReferenceActivePhysicalStep.RoundInput.row] using
      firstLaunchSlowSet_assignmentFibre_eq x v w hsampler
  have hpayload : AssignmentStartPayload.Input.ofFirstAssignment launchV =
      AssignmentStartPayload.Input.ofFirstAssignment launchW := by
    simpa [launchV, launchW, CoordinatorRoundDispatch.firstLaunchInput,
      ReferenceActivePhysicalStep.firstInput, assignmentFibreInput,
      ReferenceActivePhysicalStep.RoundInput.row] using
      firstPayload_assignmentFibre_eq x v w hsampler
  change (CoordinatorAssignmentRegisterInstall.installFirst launchV).registers =
    (CoordinatorAssignmentRegisterInstall.installFirst launchW).registers
  simp only [CoordinatorAssignmentRegisterInstall.installFirst,
    CoordinatorAssignmentRegisterInstall.firstRegisters,
    CoordinatorAssignmentRegisterInstall.firstStartRoundResult]
  rw [hpayload]
  rfl

/-- The accepted first dispatcher always returns its checked chosen branch;
its explicit nonempty-choice check makes the rejection branch impossible. -/
theorem dispatchFirst_chosen_exists (input : CoordinatorRoundDispatch.FirstInput p) :
    ∃ (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
        (CoordinatorRoundDispatch.firstLaunchInput input))
      (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
        installed.startRoundResult installed.registers.time installed.registers.complementWeights
        input.row),
      CoordinatorRoundDispatch.dispatchFirst input = .chosen installed selection := by
  classical
  unfold CoordinatorRoundDispatch.dispatchFirst
  extract_lets launch actualInstall started payload weights cutoff hpayload hstarted hcutoff
    hweights hchoice hboundary hnonempty
  split
  · contradiction
  · exact ⟨actualInstall, _, rfl⟩

/-- The actual first dispatch uses the same pre-choice arm on two assignments
in a common slow-set sampler fibre, while each dispatcher retains its own
complete start record. -/
theorem dispatchFirst_arm_assignmentFibre_eq (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (hfirst : x.state.coordinator = .first)
    (hsampler : LaunchAssignmentFibreCoupling.firstLaunchSampler p v =
      LaunchAssignmentFibreCoupling.firstLaunchSampler p w) :
    (ReferenceActivePhysicalStep.dispatch (assignmentFibreInput x v)).arm =
      (ReferenceActivePhysicalStep.dispatch (assignmentFibreInput x w)).arm := by
  let inputV := assignmentFibreInput x v
  let inputW := assignmentFibreInput x w
  have hchosenV := dispatchFirst_chosen_exists
    (ReferenceActivePhysicalStep.firstInput inputV)
  have hchosenW := dispatchFirst_chosen_exists
    (ReferenceActivePhysicalStep.firstInput inputW)
  obtain ⟨installedV, selectionV, hdispatchV⟩ := hchosenV
  obtain ⟨installedW, selectionW, hdispatchW⟩ := hchosenW
  have hregisters : installedV.registers = installedW.registers := by
    rw [ReferenceActivePhysicalStep.dispatchFirst_chosen_installation inputV
      installedV selectionV hdispatchV,
      ReferenceActivePhysicalStep.dispatchFirst_chosen_installation inputW
      installedW selectionW hdispatchW]
    exact firstRegisters_assignmentFibre_eq x v w hsampler
  have hstarted : installedV.startRoundResult = installedW.startRoundResult := by
    rw [ReferenceActivePhysicalStep.dispatchFirst_chosen_installation inputV
      installedV selectionV hdispatchV,
      ReferenceActivePhysicalStep.dispatchFirst_chosen_installation inputW
      installedW selectionW hdispatchW]
    rfl
  have htimeV := ReferenceActivePhysicalStep.dispatchFirst_chosen_time inputV
    installedV selectionV hdispatchV
  have htimeW := ReferenceActivePhysicalStep.dispatchFirst_chosen_time inputW
    installedW selectionW hdispatchW
  have hchoiceV := selectionV.armChoice_eq
  have hchoiceW := selectionW.armChoice_eq
  let choiceAt := fun
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (row : CompleteRow p) =>
    CoordinatorLocalArmChoice.coordinatorArmChoice registers.payload
      started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      registers.time registers.complementWeights row
  have hchoiceV' : choiceAt installedV.registers installedV.startRoundResult
      (assignmentFibreRow x v) = some selectionV.arm := by
    simpa [choiceAt, inputV, assignmentFibreInput,
      ReferenceActivePhysicalStep.firstInput,
      ReferenceActivePhysicalStep.RoundInput.row] using hchoiceV
  have hchoiceW' : choiceAt installedW.registers installedW.startRoundResult
      (assignmentFibreRow x w) = some selectionW.arm := by
    simpa [choiceAt, inputW, assignmentFibreInput,
      ReferenceActivePhysicalStep.firstInput,
      ReferenceActivePhysicalStep.RoundInput.row] using hchoiceW
  have htimeV' : installedV.registers.time = x.time := by
    change installedV.registers.time = x.time at htimeV
    exact htimeV
  have hpendingV : installedV.startRoundResult.pending =
      installedV.registers.pendingAtChoice := by
    rw [ReferenceActivePhysicalStep.dispatchFirst_chosen_installation inputV
      installedV selectionV hdispatchV]
    rfl
  have hrowChoice : choiceAt installedV.registers installedV.startRoundResult
      (assignmentFibreRow x v) =
        choiceAt installedV.registers installedV.startRoundResult
          (assignmentFibreRow x w) := by
    dsimp [choiceAt]
    rw [hpendingV, htimeV']
    exact coordinatorArmChoice_assignmentFibre_eq x v w
      installedV.registers.payload installedV.registers.pendingAtChoice
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
        installedV.startRoundResult.clock.u)
      installedV.registers.complementWeights
  have hregisterChoice : choiceAt installedV.registers installedV.startRoundResult
      (assignmentFibreRow x w) =
        choiceAt installedW.registers installedW.startRoundResult
          (assignmentFibreRow x w) := by
    have hpair : (installedV.registers, installedV.startRoundResult) =
        (installedW.registers, installedW.startRoundResult) := by
      exact Prod.ext hregisters hstarted
    exact congrArg (fun pair :
      CoordinatorLiveChoiceRecorderStep.Registers p rate.eta ×
        CoordinatorPhaseClock.StartRoundResult p =>
        choiceAt pair.1 pair.2 (assignmentFibreRow x w))
      hpair
  have hchoices : some selectionV.arm = some selectionW.arm := by
    calc
      some selectionV.arm =
          choiceAt installedV.registers installedV.startRoundResult
            (assignmentFibreRow x v) := hchoiceV'.symm
      _ = choiceAt installedV.registers installedV.startRoundResult
            (assignmentFibreRow x w) := hrowChoice
      _ = choiceAt installedW.registers installedW.startRoundResult
            (assignmentFibreRow x w) := hregisterChoice
      _ = some selectionW.arm := hchoiceW'
  have harm : selectionV.arm = selectionW.arm := Option.some.inj hchoices
  have hstateV : inputV.state.coordinator = .first := by
    simpa [inputV, assignmentFibreInput] using hfirst
  have hstateW : inputW.state.coordinator = .first := by
    simpa [inputW, assignmentFibreInput] using hfirst
  rw [ReferenceActivePhysicalStep.dispatch_first inputV hstateV, hdispatchV,
    ReferenceActivePhysicalStep.dispatch_first inputW hstateW, hdispatchW]
  rw [ReferenceActivePhysicalStep.first_chosen_arm inputV installedV selectionV hdispatchV,
    ReferenceActivePhysicalStep.first_chosen_arm inputW installedW selectionW hdispatchW]
  exact harm

/-- The accepted coordinator recorder keeps every runtime check and failure
while depending on the selected current row only through non-assignment
source labels. -/
theorem coordinatorRecordingRun_assignmentFibre_eq (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (input : CoordinatorRecordingOperation.Input p)
    (htime : input.time = x.time)
    (hrow : input.row = assignmentFibreRow x v) :
    CoordinatorRecordingOperation.run input =
      CoordinatorRecordingOperation.run
        { input with row := assignmentFibreRow x w } := by
  let inputW := { input with row := assignmentFibreRow x w }
  have hread (label : ContinuousControlSlice.Label p.m p.K)
      (hlabel : ¬ ∃ i : Fin (p.K + 1),
        label = ContinuousControlSlice.Label.assign i) :
      (input.row.2 input.time).1 label = (inputW.row.2 inputW.time).1 label := by
    dsimp [inputW]
    rw [hrow, htime]
    exact assignmentFibreRows_nonassignment_scalar x v w
      (nonAssignmentLabelOf label hlabel)
  have hslot : CoordinatorRecordingOperation.selectedSlot input =
      CoordinatorRecordingOperation.selectedSlot inputW := by
    unfold CoordinatorRecordingOperation.selectedSlot
    simp only [ContinuousLearningRows.sliceAt,
      ContinuousControlSlice.coordinate]
    exact congrArg CanonicalRecordingSlice.slotFromScalar
      (hread ContinuousControlSlice.Label.slot (by
        intro h
        rcases h with ⟨i, hi⟩
        cases hi))
  have hrec : CoordinatorRecordingOperation.selectedRecorder input =
      CoordinatorRecordingOperation.selectedRecorder inputW := by
    unfold CoordinatorRecordingOperation.selectedRecorder
    simp only [ContinuousLearningRows.sliceAt,
      ContinuousControlSlice.coordinate]
    exact congrArg
      (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m)
      (hread ContinuousControlSlice.Label.rec (by
        intro h
        rcases h with ⟨i, hi⟩
        cases hi))
  have hmask : CoordinatorRecordingOperation.ownMaskPasses input =
      CoordinatorRecordingOperation.ownMaskPasses inputW := by
    unfold CoordinatorRecordingOperation.ownMaskPasses
      CanonicalRecordingSlice.recordingMask
    apply propext
    constructor
    · intro h ell hell
      have hpilot :
          PublicDiscreteDraws.pilotDraw (K_pos p) ell
              (ContinuousLearningRows.sliceAt input.time input.row.2) =
            PublicDiscreteDraws.pilotDraw (K_pos p) ell
              (ContinuousLearningRows.sliceAt inputW.time inputW.row.2) := by
        have hscalar := hread (ContinuousControlSlice.Label.pilot ell) (by
          intro h
          rcases h with ⟨i, hi⟩
          cases hi)
        have hscalar' :
            ContinuousControlSlice.coordinate (ContinuousControlSlice.Label.pilot ell)
                (ContinuousLearningRows.sliceAt input.time input.row.2) =
              ContinuousControlSlice.coordinate (ContinuousControlSlice.Label.pilot ell)
                (ContinuousLearningRows.sliceAt inputW.time inputW.row.2) := by
          simpa [inputW, ContinuousLearningRows.sliceAt,
            ContinuousControlSlice.coordinate] using hscalar
        exact congrArg (PublicDiscreteDraws.pilotFromScalar p.K (K_pos p)) hscalar'
      intro heq
      exact h ell hell (hpilot.trans heq)
    · intro h ell hell
      have hpilot :
          PublicDiscreteDraws.pilotDraw (K_pos p) ell
              (ContinuousLearningRows.sliceAt input.time input.row.2) =
            PublicDiscreteDraws.pilotDraw (K_pos p) ell
              (ContinuousLearningRows.sliceAt inputW.time inputW.row.2) := by
        have hscalar := hread (ContinuousControlSlice.Label.pilot ell) (by
          intro h
          rcases h with ⟨i, hi⟩
          cases hi)
        have hscalar' :
            ContinuousControlSlice.coordinate (ContinuousControlSlice.Label.pilot ell)
                (ContinuousLearningRows.sliceAt input.time input.row.2) =
              ContinuousControlSlice.coordinate (ContinuousControlSlice.Label.pilot ell)
                (ContinuousLearningRows.sliceAt inputW.time inputW.row.2) := by
          simpa [inputW, ContinuousLearningRows.sliceAt,
            ContinuousControlSlice.coordinate] using hscalar
        exact congrArg (PublicDiscreteDraws.pilotFromScalar p.K (K_pos p)) hscalar'
      intro heq
      exact h ell hell (hpilot.symm.trans heq)
  have hthin :
      ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
          (ContinuousLearningRows.sliceAt input.time input.row.2) =
        ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
          (ContinuousLearningRows.sliceAt inputW.time inputW.row.2) := by
    simp only [ContinuousLearningRows.sliceAt,
      ContinuousControlSlice.coordinate]
    exact hread ContinuousControlSlice.Label.thin (by
      intro h
      rcases h with ⟨i, hi⟩
      cases hi)
  have hvalidW : CoordinatorRecordingOperation.InputsValid inputW ↔
      CoordinatorRecordingOperation.InputsValid input := by
    constructor
    · intro h
      exact ⟨h.sigma_le_terminal, h.boundary_le_terminal, h.eta_pos,
        h.eta_source_cap, h.anchor_pos, h.current_pos, h.anchor_le_current,
        h.current_le_twice_anchor⟩
    · intro h
      exact ⟨h.sigma_le_terminal, h.boundary_le_terminal, h.eta_pos,
        h.eta_source_cap, h.anchor_pos, h.current_pos, h.anchor_le_current,
        h.current_le_twice_anchor⟩
  unfold CoordinatorRecordingOperation.run
  by_cases hvalid : CoordinatorRecordingOperation.InputsValid input
  · have hvalid' : CoordinatorRecordingOperation.InputsValid inputW :=
      hvalidW.mpr hvalid
    rw [dif_pos hvalid, dif_pos hvalid']
    change CoordinatorRecordingOperation.executeValid input hvalid =
      CoordinatorRecordingOperation.executeValid inputW hvalid'
    have hraw : CoordinatorRecordingOperation.coordinatorRawGateMass input hvalid =
        CoordinatorRecordingOperation.coordinatorRawGateMass inputW hvalid' := by
      simp [CoordinatorRecordingOperation.coordinatorRawGateMass,
        CoordinatorRecordingOperation.coordinatorArmProbability, inputW]
    have hfloor : CoordinatorRecordingOperation.floorArrival input =
        CoordinatorRecordingOperation.floorArrival inputW := by
      simp [CoordinatorRecordingOperation.floorArrival, inputW]
    have hfrozen : CoordinatorRecordingOperation.isFrozen input =
        CoordinatorRecordingOperation.isFrozen inputW := by
      simp [CoordinatorRecordingOperation.isFrozen,
        CoordinatorRecordingOperation.sourceCalendarRound, inputW]
    have howns : CoordinatorRecordingOperation.ownsArm input.mode input.ownArm =
        CoordinatorRecordingOperation.ownsArm inputW.mode inputW.ownArm := rfl
    simp only [CoordinatorRecordingOperation.executeValid,
      hslot, hrec, hthin, hraw, hfloor, howns]
    rw [hfrozen, hmask]
  · have hvalid' : ¬ CoordinatorRecordingOperation.InputsValid inputW := by
      intro h
      exact hvalid (hvalidW.mp h)
    rw [dif_neg hvalid, dif_neg hvalid']

/-- The literal proposal bit is preserved at every calendar coordinate. The
assignment inverse split leaves the `prop` scalar outside its assignment
subtype, including at the updated current coordinate. -/
theorem assignmentFibreRows_proposalBit_eq (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (t : Fin p.T) :
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (assignmentFibreRow x v) t =
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (assignmentFibreRow x w) t := by
  have hprop :
      ((assignmentFibreRow x v).2 t).1 ContinuousControlSlice.Label.prop =
        ((assignmentFibreRow x w).2 t).1 ContinuousControlSlice.Label.prop := by
    have hleft := assignmentFibreRow_nonassignment_scalar x v
      (nonAssignmentLabelOf ContinuousControlSlice.Label.prop (by
        intro h
        rcases h with ⟨j, hj⟩
        cases hj)) t
    have hright := assignmentFibreRow_nonassignment_scalar x w
      (nonAssignmentLabelOf ContinuousControlSlice.Label.prop (by
        intro h
        rcases h with ⟨j, hj⟩
        cases hj)) t
    simpa [nonAssignmentLabelOf] using hleft.trans hright.symm
  change FollowerCutoffScan.thresholdProposalBit
      (((assignmentFibreRow x v).2 t).1 ContinuousControlSlice.Label.prop)
      (FollowerCutoffScan.proposalHazard p rate.eta.val) =
    FollowerCutoffScan.thresholdProposalBit
      (((assignmentFibreRow x w).2 t).1 ContinuousControlSlice.Label.prop)
      (FollowerCutoffScan.proposalHazard p rate.eta.val)
  exact congrArg (fun scalar => FollowerCutoffScan.thresholdProposalBit scalar
    (FollowerCutoffScan.proposalHazard p rate.eta.val)) hprop

/-- The first live confirmation update uses only the preserved slot,
selected-follower draw, and reserved DOWN affine sample from this row. -/
theorem confirmationUpdate_assignmentFibre_eq (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (payload : AssignmentStartPayload.Input p rate.eta)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (observation : Fin (D p + 1)) :
    CoordinatorLocalArmChoice.confirmationUpdate payload pending cutoff x.time
        (assignmentFibreRow x v) observation =
      CoordinatorLocalArmChoice.confirmationUpdate payload pending cutoff x.time
        (assignmentFibreRow x w) observation := by
  let rowV := assignmentFibreRow x v
  let rowW := assignmentFibreRow x w
  have hslotScalar := assignmentFibreRows_nonassignment_scalar x v w
    (nonAssignmentLabelOf ContinuousControlSlice.Label.slot (by
      intro h
      rcases h with ⟨j, hj⟩
      cases hj))
  have hselectedScalar := assignmentFibreRows_nonassignment_scalar x v w
    (nonAssignmentLabelOf ContinuousControlSlice.Label.sel (by
      intro h
      rcases h with ⟨j, hj⟩
      cases hj))
  have hslot : PublicDiscreteDraws.slotDraw (rowV.2 x.time).1 =
      PublicDiscreteDraws.slotDraw (rowW.2 x.time).1 := by
    have hs : (rowV.2 x.time).1 ContinuousControlSlice.Label.slot =
        (rowW.2 x.time).1 ContinuousControlSlice.Label.slot := by
      simpa [rowV, rowW, nonAssignmentLabelOf] using hslotScalar
    unfold PublicDiscreteDraws.slotDraw ContinuousControlSlice.coordinate
    rw [hs]
  have hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (rowV.2 x.time).1 = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (rowW.2 x.time).1 := by
    have hs : (rowV.2 x.time).1 ContinuousControlSlice.Label.sel =
        (rowW.2 x.time).1 ContinuousControlSlice.Label.sel := by
      simpa [rowV, rowW, nonAssignmentLabelOf] using hselectedScalar
    unfold PublicDiscreteDraws.selectedFollowerDraw ContinuousControlSlice.coordinate
    rw [hs]
  have hhash (i : ActiveRoundActions.Follower p.m) :
      CoordinatorLocalArmChoice.currentDownHash payload (rowV.2 x.time) i =
        CoordinatorLocalArmChoice.currentDownHash payload (rowW.2 x.time) i := by
    change AffineChannelLaw.affineHash ((rowV.2 x.time).2
        (CoordinatorLocalArmChoice.downChannel i))
          (CoordinatorLocalArmChoice.storedDownFlatWord payload i) =
      AffineChannelLaw.affineHash ((rowW.2 x.time).2
        (CoordinatorLocalArmChoice.downChannel i))
          (CoordinatorLocalArmChoice.storedDownFlatWord payload i)
    rw [assignmentFibreRows_affine_samples x v w]
  have hevent : CoordinatorLocalArmChoice.downConfirmationEvent payload pending
      cutoff x.time (rowV.2 x.time) observation ↔
    CoordinatorLocalArmChoice.downConfirmationEvent payload pending
      cutoff x.time (rowW.2 x.time) observation := by
    simp [CoordinatorLocalArmChoice.downConfirmationEvent, hslot, hselected, hhash]
  unfold CoordinatorLocalArmChoice.confirmationUpdate
  change CoordinatorLocalArmChoice.confirmationUpdateCore payload pending cutoff x.time
      (rowV.2 x.time) observation =
    CoordinatorLocalArmChoice.confirmationUpdateCore payload pending cutoff x.time
      (rowW.2 x.time) observation
  have hcore : CoordinatorLocalArmChoice.confirmationUpdateCore payload pending cutoff x.time
      (rowV.2 x.time) observation =
    CoordinatorLocalArmChoice.confirmationUpdateCore payload pending cutoff x.time
      (rowW.2 x.time) observation := by
    unfold CoordinatorLocalArmChoice.confirmationUpdateCore
    by_cases hvalid : CoordinatorLocalArmChoice.ConfirmationInputsValid payload cutoff x.time
    · simp only [dif_pos hvalid]
      by_cases heventV : CoordinatorLocalArmChoice.downConfirmationEvent payload pending
          cutoff x.time (rowV.2 x.time) observation
      · have heventW := hevent.mp heventV
        simp [heventV, heventW, hselected]
      · have heventW : ¬ CoordinatorLocalArmChoice.downConfirmationEvent payload pending
          cutoff x.time (rowW.2 x.time) observation := by
            intro h
            exact heventV (hevent.mpr h)
        simp [heventV, heventW, hselected]
    · simp [hvalid]
  exact hcore

/-- The actual phase-clock finish operation is equal across the assignment
fibre, including its proposal read and every checked clock failure. -/
theorem finishRound_assignmentFibre_eq (x : RoundInput p rate)
    (v w : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (ActiveRoundActions.Follower p.m)) :
    CoordinatorPhaseClock.finishRound p rate.eta.val x.time clock pending
        (assignmentFibreRow x v) =
      CoordinatorPhaseClock.finishRound p rate.eta.val x.time clock pending
        (assignmentFibreRow x w) := by
  have hbit := assignmentFibreRows_proposalBit_eq x v w x.time
  unfold CoordinatorPhaseClock.finishRound
  simp only [hbit]

/-- The forward-bit component of the selected complete row is retained. -/
theorem assignmentFibreRow_forward (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p) :
    (assignmentFibreRow x v).1 = x.row.1 := rfl

/-- At the updated call coordinate, the actual row projection recovers the
whole requested assignment vector. -/
theorem ownAssignmentVector_assignmentFibreRow (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p) :
    LaterAssignmentStartOperation.ownAssignmentVector (assignmentFibreRow x v) x.time = v := by
  change ContinuousControlSlice.assignmentVector
    ((assignmentFibreRow x v).2 x.time).1 = v
  rw [show (assignmentFibreRow x v).2 x.time = assignmentCoordinateUpdate x v by
    simp [assignmentFibreRow]]
  exact assignmentCoordinateUpdate_vector x v

/-- The selected whole row of each constructed input is its local fibre row.
-/
theorem assignmentFibreInput_row (x : RoundInput p rate)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p) :
    (assignmentFibreInput x v).row = assignmentFibreRow x v := by
  simp [assignmentFibreInput, RoundInput.row]

end Bandits.Support.ReferenceFirstAssignmentFibreStep

end
