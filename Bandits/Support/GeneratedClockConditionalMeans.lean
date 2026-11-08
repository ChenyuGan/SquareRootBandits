/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapFiltration
public import Bandits.Support.BootstrapModeMeans
public import Bandits.Support.BootstrapOriginalScalarLaw

/-!
# Actual generated discovery and multicast clock tests

For one real calendar block and round, this module puts the physical
DISCOVER, MULTICAST, and one-clock tests on the accepted generated descriptor
and the original entire current public/private vector.  The completion row
and scalar stream are explicit analytic inputs for the fixed-snapshot adapter;
the current-round overwrite makes every exported actual-output identity hold
for every completion.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:398-450`,
`appendix_b_communication.tex:247-292`, and
`sources/zip4/manuscript/07_public_setup.tex:40-50,76-105`.

These are internal conditional-mean constructions.  They make no claim about
block-draw freshness in the enlarged filtration, block-start laws, ID-fibre
averaging, productive-block probability, whole-block gain, startup success,
post-publication freshness, or source-statement closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.GeneratedClockConditionalMeans

open MeasureTheory
open ConstructorDimensions BootstrapDimensions CompletePublicTable
open BootstrapPrivateRoundStreams PrivateRoundFreshness
open BootstrapPhysicalBlock BootstrapModeService
open FiniteBanditModel ActiveRoundActions PublicDiscreteDraws
open BootstrapOriginalScalarLaw
open GeneratedBootstrapRoundLaw GeneratedBootstrapFiltration
open BootstrapModeMeans
open ReferenceInitializationRun
open scoped BigOperators Classical

variable {p : ConstructorDimensions.Parameters} {s : Fin (n_boot p)}

/-- A fixed-snapshot physical input assembled from the descriptor's actual
block boundary/profile/target and explicit complete-coordinate fillers.  Only
the current round is observed by the clock tests; `currentInputOf` replaces
the corresponding row and private values before any action is read. -/
def descriptorInput (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (d : Descriptor p) : BootstrapPhysicalBlock.Input p s :=
  let b := d.1
  let profile := d.2.1
  let target := d.2.2.1
  { uninformed := ReferenceInitializationRun.uninformed b
    active := fun j => (profile (BootstrapPhysicalInput.sourceFollowerIndex p j.1)).1
    held := fun j => ((profile (BootstrapPhysicalInput.sourceFollowerIndex p j.1)).2).1
    privateId := fun j => ((profile (BootstrapPhysicalInput.sourceFollowerIndex p j.1)).2).2
    ids := ids
    row := rowCompletion
    target := target
    uniform := fun i t => fullArmScalarDraw p (scalarCompletion (i, t))
    coordinatorAvoid := fun t => forbiddenArmScalarDraw p target
      (scalarCompletion (coordinator p.two_le_m, t))
    followerAvoid := fun j t => forbiddenArmScalarDraw p
      (((profile (BootstrapPhysicalInput.sourceFollowerIndex p j.1)).2).1)
      (scalarCompletion (followerPlayer p.two_le_m j.1, t))
    rewards := rewards }

/-- The actual observable DISCOVER event on the original simultaneous
public/action vector, expressed using its literal collision feedback. -/
def discoveryObservableTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (d : Descriptor p)
    (w : BootstrapOriginalScalarLaw.Observable p) : ℝ :=
  let x := descriptorInput ids rewards rowCompletion scalarCompletion s d
  let st := d.2.2.2
  if st.mode = .discover ∧ roundSlot w.1 = dataSlot ∧
      0 < feedbackOfObservable x t (coordinator p.two_le_m) w then 1 else 0

/-- The actual observable MULTICAST event, including focal membership, ID
stay, and focal collision feedback.  The incoming subtype is formed only in
the branch where the actual descriptor boundary says it is incoming. -/
def multicastObservableTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (focal : Follower p.m)
    (d : Descriptor p) (w : BootstrapOriginalScalarLaw.Observable p) : ℝ :=
  let x := descriptorInput ids rewards rowCompletion scalarCompletion s d
  let st := d.2.2.2
  if hmem : focal ∈ x.uninformed then
    let j : {j // j ∈ x.uninformed} := ⟨focal, hmem⟩
    if st.mode = .multicast ∧ roundSlot w.1 = dataSlot ∧
        x.ids (x.privateId j) t = false ∧
        0 < feedbackOfObservable x t (followerPlayer p.two_le_m focal) w then 1 else 0
  else 0

/-- Literal generated discovery test of the actual descriptor and entire
original current vector.  `none` is the stopped analytic zero. -/
def discoveryTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) :
    Option (Descriptor p) × Current p → ℝ
  | (none, _) => 0
  | (some d, c) =>
      discoveryObservableTest ids rewards rowCompletion scalarCompletion s t d
        (BootstrapOriginalScalarStep.originalScalarObservable (descriptorInput ids rewards rowCompletion
          scalarCompletion s d) d.2.2.2 t c.1 c.2)

/-- Literal generated multicast test of the actual descriptor and entire
original current vector.  Null/stopped descriptors and nonincoming focal
followers contribute analytic zero. -/
def multicastTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (focal : Follower p.m) :
    Option (Descriptor p) × Current p → ℝ
  | (none, _) => 0
  | (some d, c) =>
      multicastObservableTest ids rewards rowCompletion scalarCompletion s t focal d
        (BootstrapOriginalScalarStep.originalScalarObservable (descriptorInput ids rewards rowCompletion
          scalarCompletion s d) d.2.2.2 t c.1 c.2)

/-- The one-clock test with the manuscript's discovery scaling. -/
def oneClockTest (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (focal : Follower p.m)
    (z : Option (Descriptor p) × Current p) : ℝ :=
  discoveryTest ids rewards rowCompletion scalarCompletion s t z / 8 +
    multicastTest ids rewards rowCompletion scalarCompletion s t focal z

private theorem discoveryObservableTest_measurable (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (d : Descriptor p) :
    Measurable (discoveryObservableTest ids rewards rowCompletion scalarCompletion s t d) := by
  classical
  let x := descriptorInput ids rewards rowCompletion scalarCompletion s d
  let st := d.2.2.2
  have hslot : MeasurableSet {w : BootstrapOriginalScalarLaw.Observable p |
      roundSlot w.1 = dataSlot} :=
    (measurableSet_singleton dataSlot).preimage
      ((BootstrapModeService.measurePreserving_roundSlot p).measurable.comp measurable_fst)
  have hfeedback : MeasurableSet {w : BootstrapOriginalScalarLaw.Observable p |
      0 < feedbackOfObservable x t (coordinator p.two_le_m) w} :=
    (measurableSet_Ioi (a := (0 : ℝ))).preimage
      (BootstrapOriginalScalarLaw.measurable_feedbackOfObservable x t
        (coordinator p.two_le_m))
  change Measurable (fun w : BootstrapOriginalScalarLaw.Observable p =>
    if st.mode = BootstrapPhysicalBlock.Mode.discover ∧ roundSlot w.1 = dataSlot ∧
        0 < feedbackOfObservable x t (coordinator p.two_le_m) w then (1 : ℝ) else 0)
  by_cases hm : st.mode = BootstrapPhysicalBlock.Mode.discover
  · simpa only [hm, true_and] using
      (Measurable.ite (hslot.inter hfeedback) measurable_const measurable_const :
        Measurable (fun w : BootstrapOriginalScalarLaw.Observable p =>
          if roundSlot w.1 = dataSlot ∧
              0 < feedbackOfObservable x t (coordinator p.two_le_m) w then
            (1 : ℝ) else 0))
  · simp only [hm, false_and, ite_false]
    exact measurable_const

private theorem multicastObservableTest_measurable (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (focal : Follower p.m)
    (d : Descriptor p) :
    Measurable (multicastObservableTest ids rewards rowCompletion scalarCompletion s t focal d) := by
  classical
  let x := descriptorInput ids rewards rowCompletion scalarCompletion s d
  let st := d.2.2.2
  by_cases hmem : focal ∈ x.uninformed
  · let j : {j // j ∈ x.uninformed} := ⟨focal, hmem⟩
    have hmem' : focal ∈ (descriptorInput ids rewards rowCompletion scalarCompletion s d).uninformed := by
      simpa [x] using hmem
    unfold multicastObservableTest
    dsimp only [x, st]
    simp only [dif_pos hmem']
    have hslot : MeasurableSet {w : BootstrapOriginalScalarLaw.Observable p |
        roundSlot w.1 = dataSlot} :=
      (measurableSet_singleton dataSlot).preimage
        ((BootstrapModeService.measurePreserving_roundSlot p).measurable.comp measurable_fst)
    have hfeedback : MeasurableSet {w : BootstrapOriginalScalarLaw.Observable p |
        0 < feedbackOfObservable x t (followerPlayer p.two_le_m focal) w} :=
      (measurableSet_Ioi (a := (0 : ℝ))).preimage
        (BootstrapOriginalScalarLaw.measurable_feedbackOfObservable x t
          (followerPlayer p.two_le_m focal))
    change Measurable (fun w : BootstrapOriginalScalarLaw.Observable p =>
      if st.mode = BootstrapPhysicalBlock.Mode.multicast ∧ roundSlot w.1 = dataSlot ∧
          x.ids (x.privateId j) t = false ∧
          0 < feedbackOfObservable x t (followerPlayer p.two_le_m focal) w then
        (1 : ℝ) else 0)
    by_cases hm : st.mode = BootstrapPhysicalBlock.Mode.multicast
    · by_cases hid : x.ids (x.privateId j) t = false
      · simpa only [hm, hid, true_and] using
          (Measurable.ite (hslot.inter hfeedback) measurable_const measurable_const :
            Measurable (fun w : BootstrapOriginalScalarLaw.Observable p =>
              if roundSlot w.1 = dataSlot ∧
                  0 < feedbackOfObservable x t (followerPlayer p.two_le_m focal) w then
                (1 : ℝ) else 0))
      · simpa [hm, hid] using
          (measurable_const : Measurable (fun _ : BootstrapOriginalScalarLaw.Observable p => (0 : ℝ)))
    · simpa [hm] using
        (measurable_const : Measurable (fun _ : BootstrapOriginalScalarLaw.Observable p => (0 : ℝ)))
  · have hmem' : ¬ focal ∈ (descriptorInput ids rewards rowCompletion scalarCompletion s d).uninformed := by
      simpa [x] using hmem
    unfold multicastObservableTest
    dsimp only [x, st]
    simp only [dif_neg hmem']
    exact measurable_const

/-- Joint Borel measurability of the stopped generated discovery test. -/
theorem discoveryTest_measurable (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) :
    Measurable (discoveryTest ids rewards rowCompletion scalarCompletion s t) := by
  classical
  apply measurable_from_prod_countable_right
  intro d
  cases d with
  | none => exact measurable_const
  | some d =>
      let x := descriptorInput ids rewards rowCompletion scalarCompletion s d
      exact (discoveryObservableTest_measurable ids rewards rowCompletion
        scalarCompletion s t d).comp
        (BootstrapOriginalScalarLaw.measurable_originalScalarObservable x d.2.2.2 t)

/-- Joint Borel measurability of the stopped generated multicast test. -/
theorem multicastTest_measurable (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (focal : Follower p.m) :
    Measurable (multicastTest ids rewards rowCompletion scalarCompletion s t focal) := by
  classical
  apply measurable_from_prod_countable_right
  intro d
  cases d with
  | none => exact measurable_const
  | some d =>
      let x := descriptorInput ids rewards rowCompletion scalarCompletion s d
      exact (multicastObservableTest_measurable ids rewards rowCompletion
        scalarCompletion s t focal d).comp
        (BootstrapOriginalScalarLaw.measurable_originalScalarObservable x d.2.2.2 t)

/-- Every discovery test is a literal indicator. -/
theorem discoveryTest_unit_bounds (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (z : Option (Descriptor p) × Current p) :
    0 ≤ discoveryTest ids rewards rowCompletion scalarCompletion s t z ∧
      discoveryTest ids rewards rowCompletion scalarCompletion s t z ≤ 1 := by
  cases z with
  | mk od c => cases od <;> simp [discoveryTest, discoveryObservableTest] <;> split_ifs <;> norm_num

/-- Every multicast test is a literal indicator. -/
theorem multicastTest_unit_bounds (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (focal : Follower p.m)
    (z : Option (Descriptor p) × Current p) :
    0 ≤ multicastTest ids rewards rowCompletion scalarCompletion s t focal z ∧
      multicastTest ids rewards rowCompletion scalarCompletion s t focal z ≤ 1 := by
  cases z with
  | mk od c =>
      cases od with
      | none => simp [multicastTest]
      | some d =>
          by_cases hmem : focal ∈ (descriptorInput ids rewards rowCompletion
            scalarCompletion s d).uninformed <;>
            simp [multicastTest, multicastObservableTest, hmem] <;> split_ifs <;> norm_num

/-- The two observable tests are disjoint because their pre-choice modes are
different; hence the weighted one-clock test is also in `[0,1]`. -/
theorem oneClockTest_unit_bounds (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (focal : Follower p.m)
    (z : Option (Descriptor p) × Current p) :
    0 ≤ oneClockTest ids rewards rowCompletion scalarCompletion s t focal z ∧
      oneClockTest ids rewards rowCompletion scalarCompletion s t focal z ≤ 1 := by
  rcases z with ⟨od, c⟩
  cases od with
  | none => simp [oneClockTest, discoveryTest, multicastTest]
  | some d =>
      have hD := discoveryTest_unit_bounds ids rewards rowCompletion scalarCompletion s t
        (some d, c)
      have hM := multicastTest_unit_bounds ids rewards rowCompletion scalarCompletion s t
        focal (some d, c)
      cases hm : d.2.2.2.mode with
      | discover =>
          have hm' : d.2.2.2.mode = BootstrapPhysicalBlock.Mode.discover := hm
          have hM' : multicastTest ids rewards rowCompletion scalarCompletion s t focal
              (some d, c) = 0 := by
            simp [multicastTest, multicastObservableTest, descriptorInput,
              BootstrapOriginalScalarStep.originalScalarObservable, BootstrapOriginalScalarStep.originalScalarActions, hm']
          constructor
          · unfold oneClockTest
            exact add_nonneg (div_nonneg hD.1 (by norm_num)) hM.1
          · unfold oneClockTest
            have hscale : discoveryTest ids rewards rowCompletion scalarCompletion s t
                (some d, c) / 8 ≤ 1 := by
              nlinarith [hD.2]
            rw [hM']
            simpa using hscale
      | multicast =>
          have hm' : d.2.2.2.mode = BootstrapPhysicalBlock.Mode.multicast := hm
          have hD' : discoveryTest ids rewards rowCompletion scalarCompletion s t
              (some d, c) = 0 := by
            simp [discoveryTest, discoveryObservableTest, descriptorInput,
              BootstrapOriginalScalarStep.originalScalarObservable, BootstrapOriginalScalarStep.originalScalarActions, hm']
          constructor
          · unfold oneClockTest
            exact add_nonneg (div_nonneg hD.1 (by norm_num)) hM.1
          · unfold oneClockTest
            rw [hD']
            simpa only [zero_div, zero_add] using hM.2

/-- The conditional test-value identity supplied by the accepted actual
generated filtration. -/
theorem discoveryTest_actual_condExp_identity (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p) :
    condExp (analysisFiltration p t.val) (originalLaw p)
      (testValue p ids rewards C_star C_h eta s t
        (discoveryTest ids rewards rowCompletion scalarCompletion s t)) =ᵐ[originalLaw p]
      conditionalKernelValue p ids rewards C_star C_h eta s t
        (discoveryTest ids rewards rowCompletion scalarCompletion s t) := by
  exact GeneratedBootstrapFiltration.actual_condExp_identity p ids rewards C_star C_h eta s t ht
    (discoveryTest ids rewards rowCompletion scalarCompletion s t)
    (discoveryTest_measurable ids rewards rowCompletion scalarCompletion s t) 1 (by norm_num)
    (fun z => by
      rcases discoveryTest_unit_bounds ids rewards rowCompletion scalarCompletion s t z with
        ⟨hlo, hhi⟩
      exact abs_le.mpr ⟨by linarith, hhi⟩)

/-- The conditional test-value identity for the stopped multicast test. -/
theorem multicastTest_actual_condExp_identity (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) (focal : Follower p.m)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p) :
    condExp (analysisFiltration p t.val) (originalLaw p)
      (testValue p ids rewards C_star C_h eta s t
        (multicastTest ids rewards rowCompletion scalarCompletion s t focal)) =ᵐ[originalLaw p]
      conditionalKernelValue p ids rewards C_star C_h eta s t
        (multicastTest ids rewards rowCompletion scalarCompletion s t focal) := by
  exact GeneratedBootstrapFiltration.actual_condExp_identity p ids rewards C_star C_h eta s t ht
    (multicastTest ids rewards rowCompletion scalarCompletion s t focal)
    (multicastTest_measurable ids rewards rowCompletion scalarCompletion s t focal) 1 (by norm_num)
    (fun z => by
      rcases multicastTest_unit_bounds ids rewards rowCompletion scalarCompletion s t focal z with
        ⟨hlo, hhi⟩
      exact abs_le.mpr ⟨by linarith, hhi⟩)

/-- The one-clock conditional test-value identity. -/
theorem oneClockTest_actual_condExp_identity (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) (focal : Follower p.m)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p) :
    condExp (analysisFiltration p t.val) (originalLaw p)
      (testValue p ids rewards C_star C_h eta s t
        (oneClockTest ids rewards rowCompletion scalarCompletion s t focal)) =ᵐ[originalLaw p]
      conditionalKernelValue p ids rewards C_star C_h eta s t
        (oneClockTest ids rewards rowCompletion scalarCompletion s t focal) := by
  exact GeneratedBootstrapFiltration.actual_condExp_identity p ids rewards C_star C_h eta s t ht
    (oneClockTest ids rewards rowCompletion scalarCompletion s t focal)
    (by
      unfold oneClockTest
      exact ((discoveryTest_measurable ids rewards rowCompletion scalarCompletion s t).div_const 8).add
        (multicastTest_measurable ids rewards rowCompletion scalarCompletion s t focal)) 1
    (by norm_num)
    (fun z => by
      rcases oneClockTest_unit_bounds ids rewards rowCompletion scalarCompletion s t focal z with
        ⟨hlo, hhi⟩
      exact abs_le.mpr ⟨by linarith, hhi⟩)

/-- Bounded tests on the actual descriptor/current vector are adapted one
round later and integrable under the original coordinate law. -/
theorem testValue_adapted_integrable (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (H : Option (Descriptor p) × Current p → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, |H z| ≤ B) :
    Measurable[analysisFiltration p (t.val + 1)]
        (testValue p ids rewards C_star C_h eta s t H) ∧
      Integrable (testValue p ids rewards C_star C_h eta s t H) (originalLaw p) := by
  have hd := (measurable_descriptor p ids rewards C_star C_h eta s t ht).mono
    ((analysisFiltration p).mono (Nat.le_succ t.val)) le_rfl
  exact ⟨hH.comp (hd.prodMk (measurable_current_succ p t)),
    GeneratedBootstrapFiltration.integrable_testValue p ids rewards C_star C_h eta s t ht
      H hH B hB hbound⟩

private theorem discoveryObservableTest_currentSnapshot
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (r : BootstrapModeService.RoundCoordinates p)
    (v : BootstrapModeService.RoundPrivateValues x) :
    (if st.mode = .discover ∧ roundSlot r = dataSlot ∧
        0 < feedbackOfObservable x t (coordinator p.two_le_m)
          (r, BootstrapPhysicalBlock.actions (currentInputOf x t r v) st t)
      then 1 else 0) = discoveryIndicator x st t r v := by
  have hslot : BootstrapPhysicalBlock.slot (currentInputOf x t r v) t = roundSlot r := by
    simp [currentInputOf, currentInput, BootstrapPhysicalBlock.slot, roundSlot, roundSlice]
  unfold BootstrapModeService.discoveryIndicator
  rw [BootstrapOriginalScalarLaw.feedbackOfObservable_eq, hslot]

private theorem multicastObservableTest_currentSnapshot
    (x : BootstrapPhysicalBlock.Input p s) (st : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (j : {j // j ∈ x.uninformed})
    (r : BootstrapModeService.RoundCoordinates p)
    (v : BootstrapModeService.RoundPrivateValues x) :
    (if st.mode = .multicast ∧ roundSlot r = dataSlot ∧
        x.ids (x.privateId j) t = false ∧
        0 < feedbackOfObservable x t (followerPlayer p.two_le_m j.1)
          (r, BootstrapPhysicalBlock.actions (currentInputOf x t r v) st t)
      then 1 else 0) = multicastIndicator x st t j r v := by
  have hslot : BootstrapPhysicalBlock.slot (currentInputOf x t r v) t = roundSlot r := by
    simp [currentInputOf, currentInput, BootstrapPhysicalBlock.slot, roundSlot, roundSlice]
  unfold BootstrapModeService.multicastIndicator
  rw [BootstrapOriginalScalarLaw.feedbackOfObservable_eq, hslot]

private theorem discoveryTest_integral_eq_fixedSnapshot
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (d : Descriptor p) :
    (∫ c : Current p, discoveryTest ids rewards rowCompletion scalarCompletion s t
      (some d, c) ∂currentLaw p) =
    ∫ z : BootstrapModeService.RoundCoordinates p × BootstrapModeService.RoundPrivateValues
      (descriptorInput ids rewards rowCompletion scalarCompletion s d),
      discoveryIndicator (descriptorInput ids rewards rowCompletion scalarCompletion s d)
        d.2.2.2 t z.1 z.2 ∂currentSnapshotMeasure
          (descriptorInput ids rewards rowCompletion scalarCompletion s d) t := by
  let x := descriptorInput ids rewards rowCompletion scalarCompletion s d
  let st := d.2.2.2
  calc
    _ = ∫ w : BootstrapModeService.RoundCoordinates p × BootstrapOriginalScalarStep.OriginalScalarVector p,
        discoveryObservableTest ids rewards rowCompletion scalarCompletion s t d
          (BootstrapOriginalScalarStep.originalScalarObservable x st t w.1 w.2) ∂BootstrapOriginalScalarStep.originalScalarSnapshotMeasure x := rfl
    _ = ∫ z : BootstrapModeService.RoundCoordinates p × BootstrapModeService.RoundPrivateValues x,
        discoveryObservableTest ids rewards rowCompletion scalarCompletion s t d
          (z.1, BootstrapPhysicalBlock.actions (currentInputOf x t z.1 z.2) st t)
          ∂currentSnapshotMeasure x t :=
      BootstrapOriginalScalarLaw.integral_observable_consumer x st t
        (discoveryObservableTest ids rewards rowCompletion scalarCompletion s t d)
        (discoveryObservableTest_measurable ids rewards rowCompletion scalarCompletion s t d)
    _ = ∫ z : BootstrapModeService.RoundCoordinates p × BootstrapModeService.RoundPrivateValues x,
        discoveryIndicator x st t z.1 z.2 ∂currentSnapshotMeasure x t := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact discoveryObservableTest_currentSnapshot x st t z.1 z.2

private theorem multicastTest_integral_eq_fixedSnapshot
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (focal : Follower p.m)
    (d : Descriptor p) (hmem : focal ∈
      (descriptorInput ids rewards rowCompletion scalarCompletion s d).uninformed) :
    (∫ c : Current p, multicastTest ids rewards rowCompletion scalarCompletion s t focal
      (some d, c) ∂currentLaw p) =
    ∫ z : BootstrapModeService.RoundCoordinates p × BootstrapModeService.RoundPrivateValues
      (descriptorInput ids rewards rowCompletion scalarCompletion s d),
      multicastIndicator (descriptorInput ids rewards rowCompletion scalarCompletion s d)
        d.2.2.2 t ⟨focal, hmem⟩ z.1 z.2 ∂currentSnapshotMeasure
          (descriptorInput ids rewards rowCompletion scalarCompletion s d) t := by
  let x := descriptorInput ids rewards rowCompletion scalarCompletion s d
  let st := d.2.2.2
  let j : {j // j ∈ x.uninformed} := ⟨focal, hmem⟩
  calc
    _ = ∫ w : BootstrapModeService.RoundCoordinates p × BootstrapOriginalScalarStep.OriginalScalarVector p,
        multicastObservableTest ids rewards rowCompletion scalarCompletion s t focal d
          (BootstrapOriginalScalarStep.originalScalarObservable x st t w.1 w.2) ∂BootstrapOriginalScalarStep.originalScalarSnapshotMeasure x := rfl
    _ = ∫ z : BootstrapModeService.RoundCoordinates p × BootstrapModeService.RoundPrivateValues x,
        multicastObservableTest ids rewards rowCompletion scalarCompletion s t focal d
          (z.1, BootstrapPhysicalBlock.actions (currentInputOf x t z.1 z.2) st t)
          ∂currentSnapshotMeasure x t :=
      BootstrapOriginalScalarLaw.integral_observable_consumer x st t
        (multicastObservableTest ids rewards rowCompletion scalarCompletion s t focal d)
        (multicastObservableTest_measurable ids rewards rowCompletion scalarCompletion s t focal d)
    _ = ∫ z : BootstrapModeService.RoundCoordinates p × BootstrapModeService.RoundPrivateValues x,
        multicastIndicator x st t j z.1 z.2 ∂currentSnapshotMeasure x t := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp [multicastObservableTest, hmem, j]
      exact multicastObservableTest_currentSnapshot x st t j z.1 z.2

private theorem oneClockTest_integral_eq_fixedSnapshot
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (focal : Follower p.m)
    (d : Descriptor p) (hmem : focal ∈
      (descriptorInput ids rewards rowCompletion scalarCompletion s d).uninformed) :
    (∫ c : Current p, oneClockTest ids rewards rowCompletion scalarCompletion s t focal
      (some d, c) ∂currentLaw p) =
    ∫ z : BootstrapModeService.RoundCoordinates p × BootstrapModeService.RoundPrivateValues
      (descriptorInput ids rewards rowCompletion scalarCompletion s d),
      oneClock (descriptorInput ids rewards rowCompletion scalarCompletion s d)
        d.2.2.2 t ⟨focal, hmem⟩ z.1 z.2 ∂currentSnapshotMeasure
          (descriptorInput ids rewards rowCompletion scalarCompletion s d) t := by
  let x := descriptorInput ids rewards rowCompletion scalarCompletion s d
  let st := d.2.2.2
  let j : {j // j ∈ x.uninformed} := ⟨focal, hmem⟩
  calc
    _ = ∫ w : BootstrapModeService.RoundCoordinates p × BootstrapOriginalScalarStep.OriginalScalarVector p,
        (discoveryObservableTest ids rewards rowCompletion scalarCompletion s t d
          (BootstrapOriginalScalarStep.originalScalarObservable x st t w.1 w.2) / 8 +
         multicastObservableTest ids rewards rowCompletion scalarCompletion s t focal d
          (BootstrapOriginalScalarStep.originalScalarObservable x st t w.1 w.2)) ∂BootstrapOriginalScalarStep.originalScalarSnapshotMeasure x := rfl
    _ = ∫ z : BootstrapModeService.RoundCoordinates p × BootstrapModeService.RoundPrivateValues x,
        (discoveryObservableTest ids rewards rowCompletion scalarCompletion s t d
          (z.1, BootstrapPhysicalBlock.actions (currentInputOf x t z.1 z.2) st t) / 8 +
         multicastObservableTest ids rewards rowCompletion scalarCompletion s t focal d
          (z.1, BootstrapPhysicalBlock.actions (currentInputOf x t z.1 z.2) st t))
          ∂currentSnapshotMeasure x t :=
      BootstrapOriginalScalarLaw.integral_observable_consumer x st t
        (fun w => discoveryObservableTest ids rewards rowCompletion scalarCompletion s t d w / 8 +
          multicastObservableTest ids rewards rowCompletion scalarCompletion s t focal d w)
        ((discoveryObservableTest_measurable ids rewards rowCompletion scalarCompletion s t d).div_const 8 |>.add
          (multicastObservableTest_measurable ids rewards rowCompletion scalarCompletion s t focal d))
    _ = ∫ z : BootstrapModeService.RoundCoordinates p × BootstrapModeService.RoundPrivateValues x,
        oneClock x st t j z.1 z.2 ∂currentSnapshotMeasure x t := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [oneClock]
      simp [discoveryObservableTest, multicastObservableTest, hmem, j,
        BootstrapOriginalScalarStep.originalScalarObservable,
        BootstrapOriginalScalarStep.originalScalarActions]
      rw [discoveryObservableTest_currentSnapshot x st t z.1 z.2,
        multicastObservableTest_currentSnapshot x st t j z.1 z.2]

/-- The fixed-snapshot kernel lower bound for generated DISCOVER, transferred
from the accepted original scalar observable/action law. -/
private theorem discoveryKernel_mean_ge
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (d : Descriptor p) (j : {j // j ∈
      (descriptorInput ids rewards rowCompletion scalarCompletion s d).uninformed})
    (a : Arm p.K) (hmode : d.2.2.2.mode = .discover)
    (hactive : (descriptorInput ids rewards rowCompletion scalarCompletion s d).active j = true)
    (hheld : (descriptorInput ids rewards rowCompletion scalarCompletion s d).held j = a)
    (htarget : (descriptorInput ids rewards rowCompletion scalarCompletion s d).target = a)
    (hinactive : ∀ k : {k // k ∈
      (descriptorInput ids rewards rowCompletion scalarCompletion s d).uninformed},
      k ≠ j → (descriptorInput ids rewards rowCompletion scalarCompletion s d).active k = false) :
    conditionalKernel p (discoveryTest ids rewards rowCompletion scalarCompletion s t)
      (some d) ≥ chi (descriptorInput ids rewards rowCompletion scalarCompletion s d) t a / 8 *
        (if d.2.2.2.mode = .discover ∧
          (descriptorInput ids rewards rowCompletion scalarCompletion s d).ids
            ((descriptorInput ids rewards rowCompletion scalarCompletion s d).privateId j) t = true
         then 1 else 0) := by
  let x := descriptorInput ids rewards rowCompletion scalarCompletion s d
  rw [conditionalKernel]
  rw [discoveryTest_integral_eq_fixedSnapshot ids rewards rowCompletion scalarCompletion s t d]
  have hmean := BootstrapModeMeans.discoveryIndicator_mean_ge x d.2.2.2 t j a ht hmode
    hactive hheld htarget hinactive
  simpa only [hmode, true_and] using hmean

/-- The fixed-snapshot kernel lower bound for generated MULTICAST, with its
retained-ID and small-list inputs explicit. -/
private theorem multicastKernel_mean_ge
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (d : Descriptor p) (j : {j // j ∈
      (descriptorInput ids rewards rowCompletion scalarCompletion s d).uninformed})
    (a : Arm p.K) (hmode : d.2.2.2.mode = .multicast)
    (hmem : (descriptorInput ids rewards rowCompletion scalarCompletion s d).privateId j ∈
      d.2.2.2.list)
    (hcard : d.2.2.2.list.card ≤ L0 p)
    (hactive : (descriptorInput ids rewards rowCompletion scalarCompletion s d).active j = true)
    (hheld : (descriptorInput ids rewards rowCompletion scalarCompletion s d).held j = a)
    (htarget : (descriptorInput ids rewards rowCompletion scalarCompletion s d).target = a)
    (hinactive : ∀ k : {k // k ∈
      (descriptorInput ids rewards rowCompletion scalarCompletion s d).uninformed},
      k ≠ j → (descriptorInput ids rewards rowCompletion scalarCompletion s d).active k = false) :
    conditionalKernel p (multicastTest ids rewards rowCompletion scalarCompletion s t
      j.1) (some d) ≥ chi (descriptorInput ids rewards rowCompletion scalarCompletion s d) t a / 64 *
        (if d.2.2.2.mode = .multicast ∧
          (descriptorInput ids rewards rowCompletion scalarCompletion s d).ids
            ((descriptorInput ids rewards rowCompletion scalarCompletion s d).privateId j) t = false
         then 1 else 0) := by
  let x := descriptorInput ids rewards rowCompletion scalarCompletion s d
  rw [conditionalKernel]
  rw [multicastTest_integral_eq_fixedSnapshot ids rewards rowCompletion scalarCompletion s t j.1 d j.2]
  have hmean := BootstrapModeMeans.multicastIndicator_mean_ge x d.2.2.2 t j a ht hmem
    hcard hmode hactive hheld htarget hinactive
  simpa only [hmode, true_and] using hmean

/-- The joint fixed-snapshot kernel lower bound for the one-clock score. -/
private theorem oneClockKernel_mean_ge
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (d : Descriptor p) (j : {j // j ∈
      (descriptorInput ids rewards rowCompletion scalarCompletion s d).uninformed})
    (a : Arm p.K)
    (hactive : (descriptorInput ids rewards rowCompletion scalarCompletion s d).active j = true)
    (hheld : (descriptorInput ids rewards rowCompletion scalarCompletion s d).held j = a)
    (htarget : (descriptorInput ids rewards rowCompletion scalarCompletion s d).target = a)
    (hinactive : ∀ k : {k // k ∈
      (descriptorInput ids rewards rowCompletion scalarCompletion s d).uninformed},
      k ≠ j → (descriptorInput ids rewards rowCompletion scalarCompletion s d).active k = false)
    (hmulticast : d.2.2.2.mode = .multicast →
      (descriptorInput ids rewards rowCompletion scalarCompletion s d).privateId j ∈
        d.2.2.2.list ∧ d.2.2.2.list.card ≤ L0 p) :
    conditionalKernel p (oneClockTest ids rewards rowCompletion scalarCompletion s t j.1)
      (some d) ≥ chi (descriptorInput ids rewards rowCompletion scalarCompletion s d) t a / 64 *
        ((if d.2.2.2.mode = .discover ∧
          (descriptorInput ids rewards rowCompletion scalarCompletion s d).ids
            ((descriptorInput ids rewards rowCompletion scalarCompletion s d).privateId j) t = true
         then 1 else 0) +
         (if d.2.2.2.mode = .multicast ∧
          (descriptorInput ids rewards rowCompletion scalarCompletion s d).ids
            ((descriptorInput ids rewards rowCompletion scalarCompletion s d).privateId j) t = false
         then 1 else 0)) := by
  let x := descriptorInput ids rewards rowCompletion scalarCompletion s d
  rw [conditionalKernel]
  rw [oneClockTest_integral_eq_fixedSnapshot ids rewards rowCompletion scalarCompletion s t j.1 d j.2]
  exact BootstrapModeMeans.oneClock_integral_mean_ge x d.2.2.2 t j a ht
    hactive hheld htarget hinactive hmulticast

/-- The source clock index is the manuscript's one-based round index. -/
def sourceClockIndex (t : Fin p.T) : ℕ := t.val + 1

/-- Discovery observations indexed by the one-based source calendar clock.
Zero is used outside the selected block, while actual block rounds use the
literal generated test. -/
def discoveryClock (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) : ℕ → Coordinates p → ℝ
  | 0, _ => 0
  | n + 1, e => if hn : n < p.T then
      let t : Fin p.T := ⟨n, hn⟩
      if ht : t ∈ calendarBlock p s then
        testValue p ids rewards C_star C_h eta s t
          (discoveryTest ids rewards rowCompletion scalarCompletion s t) e
      else 0
    else 0

/-- Multicast observations on the same one-based selected-block clock. -/
def multicastClock (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : Follower p.m) : ℕ → Coordinates p → ℝ
  | 0, _ => 0
  | n + 1, e => if hn : n < p.T then
      let t : Fin p.T := ⟨n, hn⟩
      if ht : t ∈ calendarBlock p s then
        testValue p ids rewards C_star C_h eta s t
          (multicastTest ids rewards rowCompletion scalarCompletion s t focal) e
      else 0
    else 0

/-- The weighted one-clock observations on the same source index. -/
def oneClock (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : Follower p.m) : ℕ → Coordinates p → ℝ
  | 0, _ => 0
  | n + 1, e => if hn : n < p.T then
      let t : Fin p.T := ⟨n, hn⟩
      if ht : t ∈ calendarBlock p s then
        testValue p ids rewards C_star C_h eta s t
          (oneClockTest ids rewards rowCompletion scalarCompletion s t focal) e
      else 0
    else 0

/-- At a real block round, the source-indexed discovery variable is exactly
the generated current-round test. -/
theorem discoveryClock_at_sourceIndex (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (e : Coordinates p) :
    discoveryClock ids rewards C_star C_h eta rowCompletion scalarCompletion s
      (sourceClockIndex t) e =
        testValue p ids rewards C_star C_h eta s t
          (discoveryTest ids rewards rowCompletion scalarCompletion s t) e := by
  simp [discoveryClock, sourceClockIndex, t.isLt, ht]

/-- The multicast source-index equality. -/
theorem multicastClock_at_sourceIndex (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (focal : Follower p.m) (e : Coordinates p) :
    multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
      (sourceClockIndex t) e =
        testValue p ids rewards C_star C_h eta s t
          (multicastTest ids rewards rowCompletion scalarCompletion s t focal) e := by
  simp [multicastClock, sourceClockIndex, t.isLt, ht]

/-- The one-clock source-index equality. -/
theorem oneClock_at_sourceIndex (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (focal : Follower p.m) (e : Coordinates p) :
    oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
      (sourceClockIndex t) e =
        testValue p ids rewards C_star C_h eta s t
          (oneClockTest ids rewards rowCompletion scalarCompletion s t focal) e := by
  simp [oneClock, sourceClockIndex, t.isLt, ht]

/-- The discovery conditional mean is exactly the accepted interval-clock
conditional mean at the exposed source round shift. -/
theorem discoveryClock_conditionalMean_sourceIndex (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s) :
    BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
      (discoveryClock ids rewards C_star C_h eta rowCompletion scalarCompletion s)
      (sourceClockIndex t) =
    condExp (analysisFiltration p t.val) (originalLaw p)
      (testValue p ids rewards C_star C_h eta s t
        (discoveryTest ids rewards rowCompletion scalarCompletion s t)) := by
  change BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
    (discoveryClock ids rewards C_star C_h eta rowCompletion scalarCompletion s)
      (GeneratedBootstrapFiltration.sourceClockIndex p t) = _
  rw [GeneratedBootstrapFiltration.bootstrapConditionalMean_source_shift p
    (discoveryClock ids rewards C_star C_h eta rowCompletion scalarCompletion s) t]
  change condExp (analysisFiltration p t.val) (originalLaw p)
    (discoveryClock ids rewards C_star C_h eta rowCompletion scalarCompletion s
      (sourceClockIndex t)) = _
  have hclock : discoveryClock ids rewards C_star C_h eta rowCompletion scalarCompletion s
      (sourceClockIndex t) = fun e => testValue p ids rewards C_star C_h eta s t
        (discoveryTest ids rewards rowCompletion scalarCompletion s t) e := by
    funext e
    exact discoveryClock_at_sourceIndex ids rewards C_star C_h eta rowCompletion
      scalarCompletion s t ht e
  rw [hclock]

/-- The multicast conditional mean uses the same `t.val + 1` clock shift. -/
theorem multicastClock_conditionalMean_sourceIndex (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (focal : Follower p.m) :
    BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
      (multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)
      (sourceClockIndex t) =
    condExp (analysisFiltration p t.val) (originalLaw p)
      (testValue p ids rewards C_star C_h eta s t
        (multicastTest ids rewards rowCompletion scalarCompletion s t focal)) := by
  change BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
    (multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)
      (GeneratedBootstrapFiltration.sourceClockIndex p t) = _
  rw [GeneratedBootstrapFiltration.bootstrapConditionalMean_source_shift p
    (multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal) t]
  change condExp (analysisFiltration p t.val) (originalLaw p)
    (multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
      (sourceClockIndex t)) = _
  have hclock : multicastClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
      (sourceClockIndex t) = fun e => testValue p ids rewards C_star C_h eta s t
        (multicastTest ids rewards rowCompletion scalarCompletion s t focal) e := by
    funext e
    exact multicastClock_at_sourceIndex ids rewards C_star C_h eta rowCompletion
      scalarCompletion s t ht focal e
  rw [hclock]
/-- The one-clock conditional mean uses the same `t.val + 1` shift. -/
theorem oneClock_conditionalMean_sourceIndex (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (ht : t ∈ calendarBlock p s)
    (focal : Follower p.m) :
    BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
      (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)
      (sourceClockIndex t) =
    condExp (analysisFiltration p t.val) (originalLaw p)
      (testValue p ids rewards C_star C_h eta s t
        (oneClockTest ids rewards rowCompletion scalarCompletion s t focal)) := by
  change BootstrapIntervalBounds.conditionalMean (originalLaw p) (analysisFiltration p)
    (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal)
      (GeneratedBootstrapFiltration.sourceClockIndex p t) = _
  rw [GeneratedBootstrapFiltration.bootstrapConditionalMean_source_shift p
    (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal) t]
  change condExp (analysisFiltration p t.val) (originalLaw p)
    (oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
      (sourceClockIndex t)) = _
  have hclock : oneClock ids rewards C_star C_h eta rowCompletion scalarCompletion s focal
      (sourceClockIndex t) = fun e => testValue p ids rewards C_star C_h eta s t
        (oneClockTest ids rewards rowCompletion scalarCompletion s t focal) e := by
    funext e
    exact oneClock_at_sourceIndex ids rewards C_star C_h eta rowCompletion
      scalarCompletion s t ht focal e
  rw [hclock]
private theorem actual_descriptor_facts (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (t : Fin p.T) (e : Coordinates p)
    (b : ReferenceInitializationRun.Boundary p)
    (profile : PrivateSourceStreams.BlockDrawProfile p) (target : Fin p.K)
    (st : BootstrapPhysicalBlock.State p)
    (hd : descriptor p ids rewards C_star C_h eta s t e =
      some (b, (profile, (target, st)))) :
    ∃ h : b.completed < n_boot p,
      nextBlock b h = s ∧
      profile = BootstrapPhysicalInput.currentBlockDrawProfile p s b.numerators
        b.weight_ge_one (input p ids rewards C_star C_h eta e).coordinates ∧
      (physical (input p ids rewards C_star C_h eta e) b h).target = target ∧
      BootstrapPhysicalBlock.run (physical (input p ids rewards C_star C_h eta e) b h)
        t.val = st := by
  classical
  let src := input p ids rewards C_star C_h eta e
  let boundary := ReferenceInitializationRun.run src s.val
  change descriptorAtBoundary p src boundary t = some (b, (profile, (target, st))) at hd
  have hfields := (descriptorAtBoundary_eq_some_iff p src boundary b t profile target st).mp hd
  rcases hfields with ⟨hboundary, hcross, hdata⟩
  rcases hdata with ⟨hvalidBoundary, hprofileBoundary, htarget, hstate⟩
  subst b
  have hcrossRun : (ReferenceInitializationRun.run src s.val).crossing = none := by
    simpa [boundary] using hcross
  have hvalidRun : (ReferenceInitializationRun.run src s.val).completed < n_boot p := by
    simpa [boundary] using hvalidBoundary
  have hnextRun := GeneratedBootstrapRoundLaw.processed_nextBlock ids rewards C_star C_h
    eta s e hcrossRun hvalidRun
  have hnextBoundary : nextBlock boundary hvalidBoundary = s := by
    simpa [boundary] using hnextRun
  have hprofile : profile =
      BootstrapPhysicalInput.currentBlockDrawProfile p s boundary.numerators boundary.weight_ge_one
        src.coordinates := by
    calc
      profile = BootstrapPhysicalInput.currentBlockDrawProfile p
          (nextBlock boundary hvalidBoundary) boundary.numerators boundary.weight_ge_one
          src.coordinates := hprofileBoundary.symm
      _ = BootstrapPhysicalInput.currentBlockDrawProfile p s boundary.numerators boundary.weight_ge_one
          src.coordinates := by rw [hnextBoundary]
  exact ⟨hvalidBoundary, hnextBoundary, hprofile,
    by simpa [src, boundary] using htarget,
    by simpa [src, boundary] using hstate⟩
/-- The three block-draw fields in the generated descriptor are the accepted
source profile fields of the actual processed physical input. -/
private theorem descriptorInput_fields_eq_actual (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (b : ReferenceInitializationRun.Boundary p)
    (profile : PrivateSourceStreams.BlockDrawProfile p) (target : Fin p.K)
    (st : BootstrapPhysicalBlock.State p) (src : ReferenceInitializationRun.Input p)
    (h : b.completed < n_boot p)
    (hnext : nextBlock b h = s)
    (hprofile : profile = BootstrapPhysicalInput.currentBlockDrawProfile p s b.numerators
      b.weight_ge_one src.coordinates)
    (htarget : (ReferenceInitializationRun.physical src b h).target = target)
    (hidsSrc : src.ids = ids) (hrewSrc : src.rewards = rewards)
    :
    let sx := descriptorInput ids rewards rowCompletion scalarCompletion s
      (b, (profile, (target, st)))
    let ax := ReferenceInitializationRun.physical src b h
    sx.uninformed = ax.uninformed ∧ sx.active = ax.active ∧ sx.held = ax.held ∧
      sx.privateId = ax.privateId ∧ sx.target = ax.target ∧
      sx.ids = ax.ids ∧ sx.rewards = ax.rewards := by
  let sx := descriptorInput ids rewards rowCompletion scalarCompletion s
    (b, (profile, (target, st)))
  let ax := ReferenceInitializationRun.physical src b h
  cases hnext
  dsimp only [sx, ax, descriptorInput, ReferenceInitializationRun.physical,
    BootstrapPhysicalInput.blockInput]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext j
    dsimp only [BootstrapPhysicalInput.activityMap,
      BootstrapPhysicalInput.currentBlockDrawProfileMap]
    rw [hprofile]
  · funext j
    dsimp only [BootstrapPhysicalInput.heldMap,
      BootstrapPhysicalInput.currentBlockDrawProfileMap]
    rw [hprofile]
  · funext j
    dsimp only [BootstrapPhysicalInput.privateIDMap,
      BootstrapPhysicalInput.currentBlockDrawProfileMap]
    rw [hprofile]
  · exact htarget.symm
  · exact hidsSrc.symm
  · exact hrewSrc.symm
/-- On every processed actual descriptor, the action profile built from the
original current public/private vector is exactly the processed physical
block's simultaneous pre-feedback action profile. -/
theorem actual_generated_actions_eq_physical
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (e : Coordinates p)
    (b : ReferenceInitializationRun.Boundary p)
    (profile : PrivateSourceStreams.BlockDrawProfile p) (target : Fin p.K)
    (st : BootstrapPhysicalBlock.State p)
    (hdesc : descriptor p ids rewards C_star C_h eta s t e =
      some (b, (profile, (target, st)))) :
    ∀ h : b.completed < n_boot p,
    BootstrapOriginalScalarStep.originalScalarActions
      (descriptorInput ids rewards rowCompletion scalarCompletion s
        (b, (profile, (target, st)))) st t
        (GeneratedBootstrapRoundLaw.current p t e).1
        (fun i => BootstrapPhysicalInput.playerRoundScalarAt p e.2 i t) =
      BootstrapPhysicalBlock.actions
        (ReferenceInitializationRun.physical (input p ids rewards C_star C_h eta e) b h) st t := by
  classical
  obtain ⟨hvalid, hnext, hprofile, htarget, hstate⟩ :=
    actual_descriptor_facts ids rewards C_star C_h eta s t e b profile target st hdesc
  intro h
  have hh : h = hvalid := Subsingleton.elim _ _
  subst h
  cases hnext
  let src := input p ids rewards C_star C_h eta e
  let ax := ReferenceInitializationRun.physical src b hvalid
  let sx := descriptorInput ids rewards rowCompletion scalarCompletion (nextBlock b hvalid)
    (b, (profile, (target, st)))
  have htarget' : target =
      BootstrapPrivateRoundStreams.coordinatorTargetDraw p
        (BootstrapPhysicalInput.coordinatorTargetScalarAt p (nextBlock b hvalid) e.2) := by
    simpa [src, ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput,
      BootstrapPhysicalInput.targetArmMap, GeneratedBootstrapRoundLaw.input,
      ReferenceInitializationMeasurability.inputOfCoordinates] using htarget.symm
  have hphysicalAction := BootstrapOriginalScalarStep.originalScalarActions_blockInput
    (nextBlock b hvalid) (ReferenceInitializationRun.uninformed b) b.numerators
    b.weight_ge_one src.ids src.row src.rewards src.coordinates t st
  have hphysicalAction' :
      BootstrapOriginalScalarStep.originalScalarActions ax st t
        (GeneratedBootstrapRoundLaw.current p t e).1
        (fun i => BootstrapPhysicalInput.playerRoundScalarAt p e.2 i t) =
        BootstrapPhysicalBlock.actions ax st t := by
    simpa [ax, src, ReferenceInitializationRun.physical,
      GeneratedBootstrapRoundLaw.input, ReferenceInitializationMeasurability.inputOfCoordinates,
      GeneratedBootstrapRoundLaw.current, BootstrapModeService.roundCoordinates,
      BootstrapPhysicalInput.blockInput] using
      hphysicalAction
  have hsame : BootstrapOriginalScalarStep.originalScalarActions sx st t
      (GeneratedBootstrapRoundLaw.current p t e).1
      (fun i => BootstrapPhysicalInput.playerRoundScalarAt p e.2 i t) =
      BootstrapOriginalScalarStep.originalScalarActions ax st t
        (GeneratedBootstrapRoundLaw.current p t e).1
        (fun i => BootstrapPhysicalInput.playerRoundScalarAt p e.2 i t) := by
    change BootstrapOriginalScalarStep.originalScalarActions
        (descriptorInput ids rewards rowCompletion scalarCompletion (nextBlock b hvalid)
          (b, (profile, (target, st)))) st t (GeneratedBootstrapRoundLaw.current p t e).1
        (fun i => BootstrapPhysicalInput.playerRoundScalarAt p e.2 i t) =
      BootstrapOriginalScalarStep.originalScalarActions
        (ReferenceInitializationRun.physical src b hvalid) st t
        (GeneratedBootstrapRoundLaw.current p t e).1
        (fun i => BootstrapPhysicalInput.playerRoundScalarAt p e.2 i t)
    rw [hprofile, htarget']
    funext i
    simp [BootstrapOriginalScalarStep.originalScalarActions,
      src, descriptorInput, ReferenceInitializationRun.physical,
      GeneratedBootstrapRoundLaw.input, ReferenceInitializationMeasurability.inputOfCoordinates,
      BootstrapPhysicalInput.blockInput, BootstrapPhysicalInput.activityMap,
      BootstrapPhysicalInput.heldMap, BootstrapPhysicalInput.privateIDMap,
      BootstrapPhysicalInput.targetArmMap,
      BootstrapPhysicalInput.currentBlockDrawProfileMap,
      BootstrapPhysicalBlock.actions, BootstrapPhysicalBlock.coordinatorAction,
      BootstrapPhysicalBlock.followerAction, BootstrapPhysicalBlock.uninformedAction,
      BootstrapPhysicalBlock.unoccupiedAction, BootstrapPhysicalBlock.forwardProduct,
      BootstrapPhysicalBlock.slot, BootstrapPhysicalBlock.selected,
      BootstrapPhysicalBlock.pilot, BootstrapPhysicalBlock.tuple,
      BootstrapPhysicalBlock.initialUpBit, BootstrapModeService.currentInputOf,
      BootstrapModeService.currentInput,
      BootstrapOriginalScalarStep.roundPrivateValuesOfOriginalScalars,
      ActiveRoundActions.followerPlayer_followerIndex]
  exact hsame.trans hphysicalAction'
/-- The literal discovery test agrees pointwise with the processed block's
pre-choice mode, physical slot, simultaneous actions, and coordinator
collision feedback. -/
theorem actual_discoveryTest_eq_physical
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (e : Coordinates p)
    (b : ReferenceInitializationRun.Boundary p)
    (profile : PrivateSourceStreams.BlockDrawProfile p) (target : Fin p.K)
    (st : BootstrapPhysicalBlock.State p)
    (hdesc : descriptor p ids rewards C_star C_h eta s t e =
      some (b, (profile, (target, st))))
    (h : b.completed < n_boot p) :
    discoveryTest ids rewards rowCompletion scalarCompletion s t
        (descriptor p ids rewards C_star C_h eta s t e,
          GeneratedBootstrapRoundLaw.current p t e) =
      (if st.mode = .discover ∧
          BootstrapPhysicalBlock.slot
              (ReferenceInitializationRun.physical
                (input p ids rewards C_star C_h eta e) b h) t = dataSlot ∧
          0 < BootstrapPhysicalBlock.feedback
              (ReferenceInitializationRun.physical
                (input p ids rewards C_star C_h eta e) b h) st t
              (coordinator p.two_le_m)
        then 1 else 0) := by
  classical
  have hActions := actual_generated_actions_eq_physical ids rewards C_star C_h eta
    rowCompletion scalarCompletion s t e b profile target st hdesc h
  simp only [discoveryTest, hdesc, GeneratedBootstrapRoundLaw.current]
  let x := descriptorInput ids rewards rowCompletion scalarCompletion s
    (b, (profile, (target, st)))
  let ax := ReferenceInitializationRun.physical (input p ids rewards C_star C_h eta e) b h
  have hslot : roundSlot (BootstrapModeService.roundCoordinates p t e.1) =
      BootstrapPhysicalBlock.slot ax t := by
    simp [ax, ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput,
      BootstrapPhysicalBlock.slot, BootstrapModeService.roundSlot,
      BootstrapModeService.roundSlice, BootstrapModeService.roundCoordinates,
      GeneratedBootstrapRoundLaw.input,
      ReferenceInitializationMeasurability.inputOfCoordinates]
  have hfeedback : BootstrapOriginalScalarLaw.feedbackOfObservable x t
      (coordinator p.two_le_m)
      (BootstrapModeService.roundCoordinates p t e.1,
        BootstrapPhysicalBlock.actions ax st t) =
      BootstrapPhysicalBlock.feedback ax st t (coordinator p.two_le_m) := by
    simp [BootstrapOriginalScalarLaw.feedbackOfObservable, BootstrapPhysicalBlock.feedback,
      x, ax, descriptorInput, ReferenceInitializationRun.physical,
      GeneratedBootstrapRoundLaw.input, ReferenceInitializationMeasurability.inputOfCoordinates,
      BootstrapPhysicalInput.blockInput]
  have hfeedback' : BootstrapOriginalScalarLaw.feedbackOfObservable
      (descriptorInput ids rewards rowCompletion scalarCompletion s
        (b, (profile, (target, st)))) t (coordinator p.two_le_m)
      (BootstrapModeService.roundCoordinates p t e.1,
        BootstrapPhysicalBlock.actions ax st t) =
      BootstrapPhysicalBlock.feedback ax st t (coordinator p.two_le_m) := by
    simpa [x] using hfeedback
  have hActions' : BootstrapOriginalScalarStep.originalScalarActions x st t
      (BootstrapModeService.roundCoordinates p t e.1)
      (fun i => BootstrapPhysicalInput.playerRoundScalarAt p e.2 i t) =
      BootstrapPhysicalBlock.actions ax st t := by
    simpa [GeneratedBootstrapRoundLaw.current, BootstrapModeService.roundCoordinates] using hActions
  change discoveryObservableTest ids rewards rowCompletion scalarCompletion s t
      (b, (profile, (target, st)))
      (BootstrapModeService.roundCoordinates p t e.1,
        BootstrapOriginalScalarStep.originalScalarActions x st t
          (BootstrapModeService.roundCoordinates p t e.1)
          (fun i => BootstrapPhysicalInput.playerRoundScalarAt p e.2 i t)) = _
  rw [hActions']
  simp only [discoveryObservableTest]
  rw [hfeedback', hslot]
/-- The literal multicast test has the processed physical round's mode,
DATA slot, action-derived collision feedback, and descriptor's actual focal
ID as its pointwise event. -/
theorem actual_multicastTest_eq_physical
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (t : Fin p.T) (e : Coordinates p)
    (focal : Follower p.m) (b : ReferenceInitializationRun.Boundary p)
    (profile : PrivateSourceStreams.BlockDrawProfile p) (target : Fin p.K)
    (st : BootstrapPhysicalBlock.State p)
    (hdesc : descriptor p ids rewards C_star C_h eta s t e =
      some (b, (profile, (target, st))))
    (h : b.completed < n_boot p) :
    multicastTest ids rewards rowCompletion scalarCompletion s t focal
        (descriptor p ids rewards C_star C_h eta s t e,
          GeneratedBootstrapRoundLaw.current p t e) =
      (if hmem : focal ∈ (descriptorInput ids rewards rowCompletion scalarCompletion s
          (b, (profile, (target, st)))).uninformed then
        let j : {j // j ∈ (descriptorInput ids rewards rowCompletion scalarCompletion s
          (b, (profile, (target, st)))).uninformed} := ⟨focal, hmem⟩
        if st.mode = .multicast ∧
            BootstrapPhysicalBlock.slot
                (ReferenceInitializationRun.physical
                  (input p ids rewards C_star C_h eta e) b h) t = dataSlot ∧
            (descriptorInput ids rewards rowCompletion scalarCompletion s
              (b, (profile, (target, st)))).ids
                ((descriptorInput ids rewards rowCompletion scalarCompletion s
                  (b, (profile, (target, st)))).privateId j) t = false ∧
            0 < BootstrapPhysicalBlock.feedback
                (ReferenceInitializationRun.physical
                  (input p ids rewards C_star C_h eta e) b h) st t
                (followerPlayer p.two_le_m focal)
        then 1 else 0
      else 0) := by
  classical
  have hActions := actual_generated_actions_eq_physical ids rewards C_star C_h eta
    rowCompletion scalarCompletion s t e b profile target st hdesc h
  simp only [multicastTest, hdesc, GeneratedBootstrapRoundLaw.current]
  let x := descriptorInput ids rewards rowCompletion scalarCompletion s
    (b, (profile, (target, st)))
  let ax := ReferenceInitializationRun.physical (input p ids rewards C_star C_h eta e) b h
  have hslot : roundSlot (BootstrapModeService.roundCoordinates p t e.1) =
      BootstrapPhysicalBlock.slot ax t := by
    simp [ax, ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput,
      BootstrapPhysicalBlock.slot, BootstrapModeService.roundSlot,
      BootstrapModeService.roundSlice, BootstrapModeService.roundCoordinates,
      GeneratedBootstrapRoundLaw.input, ReferenceInitializationMeasurability.inputOfCoordinates]
  have hfeedback : BootstrapOriginalScalarLaw.feedbackOfObservable x t
      (followerPlayer p.two_le_m focal)
      (BootstrapModeService.roundCoordinates p t e.1,
        BootstrapPhysicalBlock.actions ax st t) =
      BootstrapPhysicalBlock.feedback ax st t (followerPlayer p.two_le_m focal) := by
    simp [BootstrapOriginalScalarLaw.feedbackOfObservable, BootstrapPhysicalBlock.feedback,
      x, ax, descriptorInput, ReferenceInitializationRun.physical,
      GeneratedBootstrapRoundLaw.input, ReferenceInitializationMeasurability.inputOfCoordinates,
      BootstrapPhysicalInput.blockInput]
  have hActions' : BootstrapOriginalScalarStep.originalScalarActions x st t
      (BootstrapModeService.roundCoordinates p t e.1)
      (fun i => BootstrapPhysicalInput.playerRoundScalarAt p e.2 i t) =
      BootstrapPhysicalBlock.actions ax st t := by
    simpa [GeneratedBootstrapRoundLaw.current, BootstrapModeService.roundCoordinates] using hActions
  change multicastObservableTest ids rewards rowCompletion scalarCompletion s t focal
      (b, (profile, (target, st)))
      (BootstrapModeService.roundCoordinates p t e.1,
        BootstrapOriginalScalarStep.originalScalarActions x st t
          (BootstrapModeService.roundCoordinates p t e.1)
          (fun i => BootstrapPhysicalInput.playerRoundScalarAt p e.2 i t)) = _
  rw [hActions']
  have hfeedback' : BootstrapOriginalScalarLaw.feedbackOfObservable
      (descriptorInput ids rewards rowCompletion scalarCompletion s
        (b, (profile, (target, st)))) t (followerPlayer p.two_le_m focal)
      (BootstrapModeService.roundCoordinates p t e.1,
        BootstrapPhysicalBlock.actions ax st t) =
      BootstrapPhysicalBlock.feedback ax st t (followerPlayer p.two_le_m focal) := by
    simpa [x] using hfeedback
  simp [multicastObservableTest, x, hslot, hfeedback']
  simp only [ax]
/-- The conditional discovery lower mean on the actual generated run.  Its
only event data are the actual descriptor's incoming/activity/held/target/
isolation values; descriptor absence contributes no event. -/
theorem actual_discovery_conditional_mean_ge (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) (focal : Follower p.m)
    (a : Arm p.K) (rowCompletion : CompleteRow p)
    (scalarCompletion : PlayerRoundScalars p) :
    ∀ᵐ e ∂originalLaw p, ∀ b (profile : PrivateSourceStreams.BlockDrawProfile p)
      (target : Fin p.K) (st : BootstrapPhysicalBlock.State p),
      descriptor p ids rewards C_star C_h eta s t e = some (b, (profile, (target, st))) →
      ∀ h : b.completed < n_boot p,
      ∀ hmem : focal ∈ (physical (input p ids rewards C_star C_h eta e) b h).uninformed,
      let x := physical (input p ids rewards C_star C_h eta e) b h
      let j : {j // j ∈ x.uninformed} := ⟨focal, hmem⟩
      (x.active j = true ∧ x.held j = a ∧ x.target = a ∧
        ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) →
      condExp (analysisFiltration p t.val) (originalLaw p)
        (testValue p ids rewards C_star C_h eta s t
          (discoveryTest ids rewards rowCompletion scalarCompletion s t)) e ≥
        chi x t a / 8 * (if st.mode = .discover ∧ x.ids (x.privateId j) t = true
          then 1 else 0) := by
  have hce := discoveryTest_actual_condExp_identity ids rewards C_star C_h eta s t ht
    rowCompletion scalarCompletion
  filter_upwards [hce] with e hce
  intro b profile target st hdesc hvalid hmem
  dsimp only
  intro hguard
  let src := input p ids rewards C_star C_h eta e
  let ax := physical src b hvalid
  let sx := descriptorInput ids rewards rowCompletion scalarCompletion s
    (b, (profile, (target, st)))
  obtain ⟨hactualValid, hnext, hprofile, htarget, hstate⟩ :=
    actual_descriptor_facts ids rewards C_star C_h eta s t e b profile target st hdesc
  have hfields := descriptorInput_fields_eq_actual ids rewards rowCompletion scalarCompletion
    s b profile target st src hactualValid hnext hprofile htarget (by
      simp [src, GeneratedBootstrapRoundLaw.input,
        ReferenceInitializationMeasurability.inputOfCoordinates]) (by
      simp [src, GeneratedBootstrapRoundLaw.input,
        ReferenceInitializationMeasurability.inputOfCoordinates])
  rcases hfields with ⟨hU, hactiveEq, hheldEq, hidEq, htargetEq, hidsEq, hrewEq⟩
  have hvalidEq : hactualValid = hvalid := Subsingleton.elim _ _
  have hstateAx : BootstrapPhysicalBlock.run ax t.val = st := by
    simpa [ax, hvalidEq] using hstate
  have hU' : sx.uninformed = ax.uninformed := by simpa [ax, hvalidEq] using hU
  have hactiveEq' : sx.active = ax.active := by simpa [ax, hvalidEq] using hactiveEq
  have hheldEq' : sx.held = ax.held := by simpa [ax, hvalidEq] using hheldEq
  have hidEq' : sx.privateId = ax.privateId := by simpa [ax, hvalidEq] using hidEq
  have htargetEq' : sx.target = ax.target := by simpa [ax, hvalidEq] using htargetEq
  have hidsEq' : sx.ids = ax.ids := by simpa [ax, hvalidEq] using hidsEq
  have hrewEq' : sx.rewards = ax.rewards := by simpa [ax, hvalidEq] using hrewEq
  have hmemSx : focal ∈ sx.uninformed := by rw [hU']; exact hmem
  let jx : {j // j ∈ ax.uninformed} := ⟨focal, by simpa [ax] using hmem⟩
  let js : {j // j ∈ sx.uninformed} := ⟨focal, hmemSx⟩
  have hjEq : js = jx := by
    apply Subtype.ext
    rfl
  have hactive : sx.active js = true := by
    rw [congrFun hactiveEq' js, hjEq]
    exact hguard.1
  have hheld : sx.held js = a := by
    rw [congrFun hheldEq' js, hjEq]
    exact hguard.2.1
  have htargetSx : sx.target = a := htargetEq'.trans hguard.2.2.1
  have hinactive : ∀ k : {j // j ∈ sx.uninformed}, k ≠ js → sx.active k = false := by
    intro k hne
    let ka : {j // j ∈ ax.uninformed} := ⟨k.1, by rw [← hU']; exact k.2⟩
    have hneA : ka ≠ jx := by
      intro heq
      apply hne
      apply Subtype.ext
      exact congrArg Subtype.val heq
    have hk := hguard.2.2.2 ka hneA
    have hkaEq : k = ka := by
      apply Subtype.ext
      rfl
    have hfun := congrFun hactiveEq' k
    rw [hfun, hkaEq]
    exact hk
  have hactiveAx : ax.active jx = true := hguard.1
  have hheldAx : ax.held jx = a := hguard.2.1
  have htargetAx : ax.target = a := hguard.2.2.1
  have hz : ax.held jx = ax.target := hheldAx.trans htargetAx.symm
  have hretain := BootstrapPhysicalBlock.run_retains_id ax jx hactiveAx hz t.val
  rw [hstateAx] at hretain
  have hretainSx : sx.privateId js ∈ st.list := by
    rw [congrFun hidEq' js, hjEq]
    exact hretain
  have hmulticast : st.mode = .multicast →
      sx.privateId js ∈ st.list ∧ st.list.card ≤ L0 p := by
    intro hm
    have hcard := BootstrapPhysicalBlock.run_multicast_list_card_le ax t.val
      (by rw [hstateAx]; exact hm)
    rw [hstateAx] at hcard
    exact ⟨hretainSx, hcard⟩
  have hce' : condExp (analysisFiltration p t.val) (originalLaw p)
      (testValue p ids rewards C_star C_h eta s t
        (discoveryTest ids rewards rowCompletion scalarCompletion s t)) e =
      conditionalKernel p (discoveryTest ids rewards rowCompletion scalarCompletion s t)
        (some (b, (profile, (target, st)))) := by
    simpa [GeneratedBootstrapFiltration.conditionalKernelValue, hdesc] using hce
  have hID : sx.ids (sx.privateId js) t = ax.ids (ax.privateId jx) t := by
    calc
      sx.ids (sx.privateId js) t = ax.ids (sx.privateId js) t := by rw [hidsEq']
      _ = ax.ids (ax.privateId js) t := by rw [congrFun hidEq' js]
      _ = ax.ids (ax.privateId jx) t := by rw [hjEq]
  have hchi : chi ax t a = chi sx t a := by
    simp only [BootstrapModeService.chi]
    rw [hrewEq']
  cases hm : st.mode with
  | discover =>
      have hkernel := discoveryKernel_mean_ge ids rewards rowCompletion scalarCompletion s t ht
        (b, (profile, (target, st))) js a hm hactive hheld htargetSx hinactive
      rw [hID] at hkernel
      rw [← hchi] at hkernel
      rw [hce']
      simpa [hm] using hkernel
  | multicast =>
      have hkernelNonneg :=
        (GeneratedBootstrapFiltration.conditionalKernel_unit_bounds p
          (discoveryTest ids rewards rowCompletion scalarCompletion s t)
          (discoveryTest_measurable ids rewards rowCompletion scalarCompletion s t)
          (fun z => discoveryTest_unit_bounds ids rewards rowCompletion scalarCompletion s t z)
          (some (b, (profile, (target, st))))).1
      rw [hce']
      simpa [hm] using hkernelNonneg
/-- The actual generated multicast lower mean. The retained-ID and small-list
premises are derived from the processed physical run in this proof. -/
theorem actual_multicast_conditional_mean_ge (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) (focal : Follower p.m)
    (a : Arm p.K) (rowCompletion : CompleteRow p)
    (scalarCompletion : PlayerRoundScalars p) :
    ∀ᵐ e ∂originalLaw p, ∀ b (profile : PrivateSourceStreams.BlockDrawProfile p)
      (target : Fin p.K) (st : BootstrapPhysicalBlock.State p),
      descriptor p ids rewards C_star C_h eta s t e = some (b, (profile, (target, st))) →
      ∀ h : b.completed < n_boot p,
      ∀ hmem : focal ∈ (physical (input p ids rewards C_star C_h eta e) b h).uninformed,
      let x := physical (input p ids rewards C_star C_h eta e) b h
      let j : {j // j ∈ x.uninformed} := ⟨focal, hmem⟩
      (x.active j = true ∧ x.held j = a ∧ x.target = a ∧
        ∀ k : {j // j ∈ x.uninformed}, k ≠ j → x.active k = false) →
      condExp (analysisFiltration p t.val) (originalLaw p)
        (testValue p ids rewards C_star C_h eta s t
          (multicastTest ids rewards rowCompletion scalarCompletion s t focal)) e ≥
        chi x t a / 64 * (if st.mode = .multicast ∧
          x.ids (x.privateId j) t = false then 1 else 0) := by
  have hce := multicastTest_actual_condExp_identity ids rewards C_star C_h eta s t ht focal
    rowCompletion scalarCompletion
  filter_upwards [hce] with e hce
  intro b profile target st hdesc hvalid hmem
  dsimp only
  intro hguard
  let src := input p ids rewards C_star C_h eta e
  let ax := physical src b hvalid
  let sx := descriptorInput ids rewards rowCompletion scalarCompletion s
    (b, (profile, (target, st)))
  obtain ⟨hactualValid, hnext, hprofile, htarget, hstate⟩ :=
    actual_descriptor_facts ids rewards C_star C_h eta s t e b profile target st hdesc
  have hfields := descriptorInput_fields_eq_actual ids rewards rowCompletion scalarCompletion
    s b profile target st src hactualValid hnext hprofile htarget (by
      simp [src, GeneratedBootstrapRoundLaw.input,
        ReferenceInitializationMeasurability.inputOfCoordinates]) (by
      simp [src, GeneratedBootstrapRoundLaw.input,
        ReferenceInitializationMeasurability.inputOfCoordinates])
  rcases hfields with ⟨hU, hactiveEq, hheldEq, hidEq, htargetEq, hidsEq, hrewEq⟩
  have hvalidEq : hactualValid = hvalid := Subsingleton.elim _ _
  have hstateAx : BootstrapPhysicalBlock.run ax t.val = st := by
    simpa [ax, hvalidEq] using hstate
  have hU' : sx.uninformed = ax.uninformed := by simpa [ax, hvalidEq] using hU
  have hactiveEq' : sx.active = ax.active := by simpa [ax, hvalidEq] using hactiveEq
  have hheldEq' : sx.held = ax.held := by simpa [ax, hvalidEq] using hheldEq
  have hidEq' : sx.privateId = ax.privateId := by simpa [ax, hvalidEq] using hidEq
  have htargetEq' : sx.target = ax.target := by simpa [ax, hvalidEq] using htargetEq
  have hidsEq' : sx.ids = ax.ids := by simpa [ax, hvalidEq] using hidsEq
  have hrewEq' : sx.rewards = ax.rewards := by simpa [ax, hvalidEq] using hrewEq
  have hmemSx : focal ∈ sx.uninformed := by rw [hU']; exact hmem
  let jx : {j // j ∈ ax.uninformed} := ⟨focal, by simpa [ax] using hmem⟩
  let js : {j // j ∈ sx.uninformed} := ⟨focal, hmemSx⟩
  have hjEq : js = jx := by
    apply Subtype.ext
    rfl
  have hactive : sx.active js = true := by
    rw [congrFun hactiveEq' js, hjEq]
    exact hguard.1
  have hheld : sx.held js = a := by
    rw [congrFun hheldEq' js, hjEq]
    exact hguard.2.1
  have htargetSx : sx.target = a := htargetEq'.trans hguard.2.2.1
  have hinactive : ∀ k : {j // j ∈ sx.uninformed}, k ≠ js → sx.active k = false := by
    intro k hne
    let ka : {j // j ∈ ax.uninformed} := ⟨k.1, by rw [← hU']; exact k.2⟩
    have hneA : ka ≠ jx := by
      intro heq
      apply hne
      apply Subtype.ext
      exact congrArg Subtype.val heq
    have hk := hguard.2.2.2 ka hneA
    have hkaEq : k = ka := by
      apply Subtype.ext
      rfl
    have hfun := congrFun hactiveEq' k
    rw [hfun, hkaEq]
    exact hk
  have hactiveAx : ax.active jx = true := hguard.1
  have hheldAx : ax.held jx = a := hguard.2.1
  have htargetAx : ax.target = a := hguard.2.2.1
  have hz : ax.held jx = ax.target := hheldAx.trans htargetAx.symm
  have hretain := BootstrapPhysicalBlock.run_retains_id ax jx hactiveAx hz t.val
  rw [hstateAx] at hretain
  have hretainSx : sx.privateId js ∈ st.list := by
    rw [congrFun hidEq' js, hjEq]
    exact hretain
  have hmulticast : st.mode = .multicast →
      sx.privateId js ∈ st.list ∧ st.list.card ≤ L0 p := by
    intro hm
    have hcard := BootstrapPhysicalBlock.run_multicast_list_card_le ax t.val
      (by rw [hstateAx]; exact hm)
    rw [hstateAx] at hcard
    exact ⟨hretainSx, hcard⟩
  have hce' : condExp (analysisFiltration p t.val) (originalLaw p)
      (testValue p ids rewards C_star C_h eta s t
        (multicastTest ids rewards rowCompletion scalarCompletion s t focal)) e =
      conditionalKernel p (multicastTest ids rewards rowCompletion scalarCompletion s t focal)
        (some (b, (profile, (target, st)))) := by
    simpa [GeneratedBootstrapFiltration.conditionalKernelValue, hdesc] using hce
  have hID : sx.ids (sx.privateId js) t = ax.ids (ax.privateId jx) t := by
    calc
      sx.ids (sx.privateId js) t = ax.ids (sx.privateId js) t := by rw [hidsEq']
      _ = ax.ids (ax.privateId js) t := by rw [congrFun hidEq' js]
      _ = ax.ids (ax.privateId jx) t := by rw [hjEq]
  have hchi : chi ax t a = chi sx t a := by
    simp only [BootstrapModeService.chi]
    rw [hrewEq']
  cases hm : st.mode with
  | discover =>
      have hkernelNonneg :=
        (GeneratedBootstrapFiltration.conditionalKernel_unit_bounds p
          (multicastTest ids rewards rowCompletion scalarCompletion s t focal)
          (multicastTest_measurable ids rewards rowCompletion scalarCompletion s t focal)
          (fun z => multicastTest_unit_bounds ids rewards rowCompletion scalarCompletion s t focal z)
          (some (b, (profile, (target, st))))).1
      rw [hce']
      simpa [hm] using hkernelNonneg
  | multicast =>
      have hlist := hmulticast hm
      have hkernel := multicastKernel_mean_ge ids rewards rowCompletion scalarCompletion s t ht
        (b, (profile, (target, st))) js a hm hlist.1 hlist.2 hactive hheld htargetSx hinactive
      rw [hID] at hkernel
      rw [← hchi] at hkernel
      rw [hce']
      simpa [hm] using hkernel
/-- The actual generated one-clock lower mean with the source's combined
DISCOVER/MULTICAST indicator. -/
theorem actual_oneClock_conditional_mean_ge (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) (focal : Follower p.m)
    (a : Arm p.K) (rowCompletion : CompleteRow p)
    (scalarCompletion : PlayerRoundScalars p) :
    ∀ᵐ e ∂originalLaw p, ∀ b (profile : PrivateSourceStreams.BlockDrawProfile p)
      (target : Fin p.K) (st : BootstrapPhysicalBlock.State p),
      descriptor p ids rewards C_star C_h eta s t e = some (b, (profile, (target, st))) →
      ∀ h : b.completed < n_boot p,
      ∀ hmem : focal ∈ (physical (input p ids rewards C_star C_h eta e) b h).uninformed,
      let x := physical (input p ids rewards C_star C_h eta e) b h
      let j : {j // j ∈ x.uninformed} := ⟨focal, hmem⟩
      (x.active j = true ∧ x.held j = a ∧ x.target = a ∧
        ∀ k : {j // j ∈ x.uninformed}, k ≠ j → x.active k = false) →
      condExp (analysisFiltration p t.val) (originalLaw p)
        (testValue p ids rewards C_star C_h eta s t
          (oneClockTest ids rewards rowCompletion scalarCompletion s t focal)) e ≥
        chi x t a / 64 *
          ((if st.mode = .discover ∧ x.ids (x.privateId j) t = true then 1 else 0) +
           (if st.mode = .multicast ∧ x.ids (x.privateId j) t = false then 1 else 0)) := by
  have hce := oneClockTest_actual_condExp_identity ids rewards C_star C_h eta s t ht focal
    rowCompletion scalarCompletion
  filter_upwards [hce] with e hce
  intro b profile target st hdesc hvalid hmem
  dsimp only
  intro hguard
  let src := input p ids rewards C_star C_h eta e
  let ax := physical src b hvalid
  let sx := descriptorInput ids rewards rowCompletion scalarCompletion s
    (b, (profile, (target, st)))
  obtain ⟨hactualValid, hnext, hprofile, htarget, hstate⟩ :=
    actual_descriptor_facts ids rewards C_star C_h eta s t e b profile target st hdesc
  have hfields := descriptorInput_fields_eq_actual ids rewards rowCompletion scalarCompletion
    s b profile target st src hactualValid hnext hprofile htarget (by
      simp [src, GeneratedBootstrapRoundLaw.input,
        ReferenceInitializationMeasurability.inputOfCoordinates]) (by
      simp [src, GeneratedBootstrapRoundLaw.input,
        ReferenceInitializationMeasurability.inputOfCoordinates])
  rcases hfields with ⟨hU, hactiveEq, hheldEq, hidEq, htargetEq, hidsEq, hrewEq⟩
  have hvalidEq : hactualValid = hvalid := Subsingleton.elim _ _
  have hstateAx : BootstrapPhysicalBlock.run ax t.val = st := by
    simpa [ax, hvalidEq] using hstate
  have hU' : sx.uninformed = ax.uninformed := by simpa [ax, hvalidEq] using hU
  have hactiveEq' : sx.active = ax.active := by simpa [ax, hvalidEq] using hactiveEq
  have hheldEq' : sx.held = ax.held := by simpa [ax, hvalidEq] using hheldEq
  have hidEq' : sx.privateId = ax.privateId := by simpa [ax, hvalidEq] using hidEq
  have htargetEq' : sx.target = ax.target := by simpa [ax, hvalidEq] using htargetEq
  have hidsEq' : sx.ids = ax.ids := by simpa [ax, hvalidEq] using hidsEq
  have hrewEq' : sx.rewards = ax.rewards := by simpa [ax, hvalidEq] using hrewEq
  have hmemSx : focal ∈ sx.uninformed := by rw [hU']; exact hmem
  let jx : {j // j ∈ ax.uninformed} := ⟨focal, by simpa [ax] using hmem⟩
  let js : {j // j ∈ sx.uninformed} := ⟨focal, hmemSx⟩
  have hjEq : js = jx := by
    apply Subtype.ext
    rfl
  have hactive : sx.active js = true := by
    rw [congrFun hactiveEq' js, hjEq]
    exact hguard.1
  have hheld : sx.held js = a := by
    rw [congrFun hheldEq' js, hjEq]
    exact hguard.2.1
  have htargetSx : sx.target = a := htargetEq'.trans hguard.2.2.1
  have hinactive : ∀ k : {j // j ∈ sx.uninformed}, k ≠ js → sx.active k = false := by
    intro k hne
    let ka : {j // j ∈ ax.uninformed} := ⟨k.1, by rw [← hU']; exact k.2⟩
    have hneA : ka ≠ jx := by
      intro heq
      apply hne
      apply Subtype.ext
      exact congrArg Subtype.val heq
    have hk := hguard.2.2.2 ka hneA
    have hkaEq : k = ka := by
      apply Subtype.ext
      rfl
    have hfun := congrFun hactiveEq' k
    rw [hfun, hkaEq]
    exact hk
  have hactiveAx : ax.active jx = true := hguard.1
  have hheldAx : ax.held jx = a := hguard.2.1
  have htargetAx : ax.target = a := hguard.2.2.1
  have hz : ax.held jx = ax.target := hheldAx.trans htargetAx.symm
  have hretain := BootstrapPhysicalBlock.run_retains_id ax jx hactiveAx hz t.val
  rw [hstateAx] at hretain
  have hretainSx : sx.privateId js ∈ st.list := by
    rw [congrFun hidEq' js, hjEq]
    exact hretain
  have hmulticast : st.mode = .multicast →
      sx.privateId js ∈ st.list ∧ st.list.card ≤ L0 p := by
    intro hm
    have hcard := BootstrapPhysicalBlock.run_multicast_list_card_le ax t.val
      (by rw [hstateAx]; exact hm)
    rw [hstateAx] at hcard
    exact ⟨hretainSx, hcard⟩
  have hce' : condExp (analysisFiltration p t.val) (originalLaw p)
      (testValue p ids rewards C_star C_h eta s t
        (oneClockTest ids rewards rowCompletion scalarCompletion s t focal)) e =
      conditionalKernel p (oneClockTest ids rewards rowCompletion scalarCompletion s t focal)
        (some (b, (profile, (target, st)))) := by
    simpa [GeneratedBootstrapFiltration.conditionalKernelValue, hdesc] using hce
  have hID : sx.ids (sx.privateId js) t = ax.ids (ax.privateId jx) t := by
    calc
      sx.ids (sx.privateId js) t = ax.ids (sx.privateId js) t := by rw [hidsEq']
      _ = ax.ids (ax.privateId js) t := by rw [congrFun hidEq' js]
      _ = ax.ids (ax.privateId jx) t := by rw [hjEq]
  have hchi : chi ax t a = chi sx t a := by
    simp only [BootstrapModeService.chi]
    rw [hrewEq']
  have hkernel := oneClockKernel_mean_ge ids rewards rowCompletion scalarCompletion s t ht
    (b, (profile, (target, st))) js a hactive hheld htargetSx hinactive hmulticast
  rw [hID] at hkernel
  rw [← hchi] at hkernel
  rw [hce']
  exact hkernel

end Bandits.Support.GeneratedClockConditionalMeans
end
