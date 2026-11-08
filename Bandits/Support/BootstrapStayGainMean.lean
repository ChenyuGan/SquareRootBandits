/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapModeMeans
public import Bandits.Support.BootstrapStayAvoidance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Fixed-snapshot DATA stay-positive means

This file proves a fixed-current-snapshot lower bound for the existing
`dataStayPositive` indicator. The sampled row and all original private arm
coordinates remain jointly present while the coordinator complement draw is
factored out.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:485-506` and
`sources/zip4/manuscript/07_public_setup.tex:27-38,55-109`.

These are fixed-state snapshot statements. They do not give a conditional mean
under a reachable history or an expectation under the adaptive block law.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.BootstrapStayGainMean

open ConstructorDimensions BootstrapDimensions FiniteBanditModel
open BootstrapPhysicalBlock BootstrapModeService BootstrapModeMeans
open BootstrapStayAvoidance PublicDiscreteDraws MeasureTheory
open scoped BigOperators Classical

variable {p : ConstructorDimensions.Parameters} {s : Fin (n_boot p)}

/-- The exact coordinator-avoidance event in a fixed current snapshot. In
DISCOVER the target is used; in MULTICAST a released row uses the existing
coordinator complement draw. -/
def coordinatorSafeSet
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p)
    (a : Arm p.K) : Set (RoundCoordinates p × RoundPrivateValues x) :=
  {w | st.mode = .discover ∨
    (st.mode = .multicast ∧
      (w.1.1 ∉ forwardReleaseSet p st.list ∨ w.2.2.1.val ≠ a))}

/-- The exact current-snapshot event on which the existing physical DATA
stay-positive indicator is one, once the fixed block inputs are supplied. -/
def dataStayPositiveEvent
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (a : Arm p.K) :
    Set (RoundCoordinates p × RoundPrivateValues x) :=
  {w | x.active j = true ∧ x.ids (x.privateId j) t = false ∧
    chi x t a = 1 ∧ w ∈ dataPeerAvoidEvent x t j a ∧
      w ∈ coordinatorSafeSet x st a}

private theorem currentInputOf_slot (x : BootstrapPhysicalBlock.Input p s)
    (t : Fin p.T) (r : RoundCoordinates p) (d : RoundPrivateValues x) :
    BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = roundSlot r := by
  simp [currentInputOf, currentInput, BootstrapPhysicalBlock.slot,
    roundSlot, roundSlice]

private theorem otherPlayersAvoid_iff_peerDataAvoid
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (r : RoundCoordinates p)
    (d : RoundPrivateValues x) (a : Arm p.K)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false)
    (hdata : roundSlot r = dataSlot) :
    (∀ q : Player p.m, q ≠ ActiveRoundActions.coordinator p.two_le_m →
      q ≠ followerPlayer p.two_le_m j.1 →
        BootstrapPhysicalBlock.actions (currentInputOf x t r d) st t q ≠ a) ↔
      ∀ i : Peer x j, peerDataArms x j (r, d) i ≠ a := by
  have hslot : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = dataSlot := by
    rw [currentInputOf_slot]
    exact hdata
  constructor
  · intro h i
    have haction := peerAction_eq_peerDataArms x st t j i r d hslot hinactive
    have havoid := h i.1 (peer_ne_coordinator x j i) (peer_ne_distinguished x j i)
    rw [haction] at havoid
    exact havoid
  · intro h q hcoord hfollow
    have hmem : q ∈ peerPlayers x j := by
      simp [peerPlayers, hcoord, hfollow]
    let i : Peer x j := ⟨q, hmem⟩
    have haction := peerAction_eq_peerDataArms x st t j i r d hslot hinactive
    rw [haction]
    exact h i

private theorem coordinatorCondition_iff_release
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (r : RoundCoordinates p) (d : RoundPrivateValues x) (a : Arm p.K) :
    (st.mode = .discover ∨
      (st.mode = .multicast ∧
        (BootstrapPhysicalBlock.forwardProduct (currentInputOf x t r d) st t ≠ 1 ∨
          (BootstrapPhysicalBlock.forwardProduct (currentInputOf x t r d) st t = 1 ∧
            ((currentInputOf x t r d).coordinatorAvoid t).val ≠ a)))) ↔
    (st.mode = .discover ∨
      (st.mode = .multicast ∧
        (r.1 ∉ forwardReleaseSet p st.list ∨ d.2.1.val ≠ a))) := by
  have hcoord : ((currentInputOf x t r d).coordinatorAvoid t).val = d.2.1.val := by
    simp [currentInputOf, currentInput]
  by_cases hdiscover : st.mode = .discover
  · simp [hdiscover]
  · by_cases hmulticast : st.mode = .multicast
    · by_cases hrelease : r.1 ∈ forwardReleaseSet p st.list
      · simp [hmulticast, hcoord, hrelease, currentForwardProduct_eq_one_iff_release]
      · simp [hmulticast, hcoord, hrelease, currentForwardProduct_eq_one_iff_release]
    · simp [hdiscover, hmulticast]

private theorem dataStayPositive_eq_one_iff_event
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (a z : Arm p.K)
    (r : RoundCoordinates p) (d : RoundPrivateValues x)
    (hheld : x.held j = a)
    (htarget : x.target = z) (hza : z ≠ a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    dataStayPositive x st t j r d = 1 ↔
      (r, d) ∈ dataStayPositiveEvent x st t j a := by
  by_cases hdata : roundSlot r = dataSlot
  · have hchar := dataStayPositive_eq_one_iff x st t j r d a z htarget hheld hza hdata
    have hcoord := coordinatorCondition_iff_release x st t r d a
    have hpeers := otherPlayersAvoid_iff_peerDataAvoid x st t j r d a hinactive hdata
    have hslot := currentInputOf_slot x t r d
    constructor
    · intro hone
      rcases hchar.mp hone with ⟨hactive', hid, hchi, _hslot, hmode, hother⟩
      refine ⟨hactive', hid, hchi, ?_, hcoord.mp hmode⟩
      simp only [dataPeerAvoidEvent, Set.mem_ofPred_eq, peerDataAvoidSet]
      exact ⟨hdata, hpeers.mp hother⟩
    · rintro ⟨hactive', hid, hchi, hbase, hmode⟩
      simp only [dataPeerAvoidEvent, Set.mem_ofPred_eq, peerDataAvoidSet] at hbase
      have hother := hpeers.mpr hbase.2
      have hslot' : BootstrapPhysicalBlock.slot (currentInputOf x t r d) t = dataSlot := by
        rw [hslot]
        exact hbase.1
      exact hchar.mpr ⟨hactive', hid, hchi, hslot', hcoord.mpr hmode, hother⟩
  · have hslot := currentInputOf_slot x t r d
    constructor
    · intro hone
      unfold dataStayPositive at hone
      split_ifs at hone with hconditions
      · exact False.elim (hdata (by simpa [hslot] using hconditions.2.2.1))
      · norm_num at hone
    · intro hevent
      have hbase := hevent.2.2.2.1
      simp only [dataPeerAvoidEvent, Set.mem_ofPred_eq] at hbase
      exact False.elim (hdata hbase.1)

/-- The mode-dependent part of the event is measurable with respect to the
same snapshot product: DATA peer coordinates, the actual release row, and the
existing coordinator complement value. -/
theorem dataStayPositiveEvent_measurable
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (a : Arm p.K) :
    MeasurableSet (dataStayPositiveEvent x st t j a) := by
  have hbase := dataPeerAvoidEvent_measurable x t j a
  have hrelease : MeasurableSet
      {w : RoundCoordinates p × RoundPrivateValues x |
        w.1.1 ∈ forwardReleaseSet p st.list} := by
    exact (forwardReleaseSet_measurable p st.list).preimage
      (measurable_fst.comp measurable_fst)
  have hcoordFn : Measurable
      (fun w : RoundCoordinates p × RoundPrivateValues x => w.2.2.1.val) :=
    measurable_subtype_coe.comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have havoid : MeasurableSet
      {w : RoundCoordinates p × RoundPrivateValues x | w.2.2.1.val ≠ a} := by
    exact (measurableSet_singleton a).compl.preimage hcoordFn
  have hmodeSet : MeasurableSet (coordinatorSafeSet x st a) := by
    by_cases hdiscover : st.mode = .discover
    · have heq : coordinatorSafeSet x st a = Set.univ := by
        ext w
        simp [coordinatorSafeSet, hdiscover]
      rw [heq]
      exact MeasurableSet.univ
    · by_cases hmulticast : st.mode = .multicast
      · have heq : coordinatorSafeSet x st a =
            ({w : RoundCoordinates p × RoundPrivateValues x |
              w.1.1 ∉ forwardReleaseSet p st.list} ∪
              {w | w.2.2.1.val ≠ a}) := by
          ext w
          simp [coordinatorSafeSet, hmulticast]
        rw [heq]
        exact hrelease.compl.union havoid
      · have heq : coordinatorSafeSet x st a = ∅ := by
          ext w
          simp [coordinatorSafeSet, hdiscover, hmulticast]
        rw [heq]
        exact MeasurableSet.empty
  by_cases hactive : x.active j = true
  · by_cases hid : x.ids (x.privateId j) t = false
    · by_cases hchi : chi x t a = 1
      · have heq : dataStayPositiveEvent x st t j a =
            dataPeerAvoidEvent x t j a ∩ coordinatorSafeSet x st a := by
          ext w
          simp [dataStayPositiveEvent, hactive, hid, hchi]
        rw [heq]
        exact hbase.inter hmodeSet
      · simp [dataStayPositiveEvent, hactive, hid, hchi]
    · simp [dataStayPositiveEvent, hactive, hid]
  · simp [dataStayPositiveEvent, hactive]

/-- On the stipulated fixed inputs, the existing physical indicator is the
indicator of `dataStayPositiveEvent`. -/
theorem dataStayPositive_eq_event_indicator
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (a z : Arm p.K)
    (hheld : x.held j = a)
    (htarget : x.target = z) (hza : z ≠ a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    (fun w : RoundCoordinates p × RoundPrivateValues x =>
      dataStayPositive x st t j w.1 w.2) =
      (dataStayPositiveEvent x st t j a).indicator (fun _ => (1 : ℝ)) := by
  funext w
  have hchar := dataStayPositive_eq_one_iff_event x st t j a z w.1 w.2
    hheld htarget hza hinactive
  by_cases hmem : w ∈ dataStayPositiveEvent x st t j a
  · have hone : dataStayPositive x st t j w.1 w.2 = 1 := hchar.mpr hmem
    simp [hmem, hone]
  · have hnotone : dataStayPositive x st t j w.1 w.2 ≠ 1 :=
      fun hone => hmem (hchar.mp hone)
    have hzero : dataStayPositive x st t j w.1 w.2 = 0 := by
      unfold dataStayPositive
      split_ifs with h
      · have hone : dataStayPositive x st t j w.1 w.2 = 1 := by
          simp [dataStayPositive, h]
        exact False.elim (hnotone hone)
      · rfl
    simp [hmem, hzero]

/-- The existing physical DATA stay-positive indicator is measurable under
the existing `currentSnapshotMeasure x t`. -/
theorem dataStayPositive_measurable
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (a z : Arm p.K)
    (hheld : x.held j = a)
    (htarget : x.target = z) (hza : z ≠ a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    Measurable (fun w : RoundCoordinates p × RoundPrivateValues x =>
      dataStayPositive x st t j w.1 w.2) := by
  rw [dataStayPositive_eq_event_indicator x st t j a z hheld
    htarget hza hinactive]
  exact measurable_const.indicator
    (dataStayPositiveEvent_measurable x st t j a)

/-- The existing physical DATA stay-positive indicator is integrable under
the same current-snapshot measure on which its mean is stated. -/
theorem dataStayPositive_integrable
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (a z : Arm p.K)
    (hheld : x.held j = a)
    (htarget : x.target = z) (hza : z ≠ a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false) :
    Integrable (fun w : RoundCoordinates p × RoundPrivateValues x =>
      dataStayPositive x st t j w.1 w.2) (currentSnapshotMeasure x t) := by
  rw [dataStayPositive_eq_event_indicator x st t j a z hheld
    htarget hza hinactive]
  exact (integrable_const (1 : ℝ)).indicator
    (dataStayPositiveEvent_measurable x st t j a)

private theorem originalDataPeerEvent_measurable
    (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) (a : Arm p.K) :
    MeasurableSet
      {q : RoundCoordinates p × (Player p.m → Arm p.K) |
        roundSlot q.1 = dataSlot ∧
          ∀ i : Peer x j, peerDataArmsFromCoordinatesUniform x j q i ≠ a} := by
  have hslot : Measurable (fun q : RoundCoordinates p × (Player p.m → Arm p.K) =>
      roundSlot q.1) := (measurePreserving_roundSlot p).measurable.comp measurable_fst
  have hpeer : Measurable
      (fun q : RoundCoordinates p × (Player p.m → Arm p.K) =>
        peerDataArmsFromCoordinatesUniform x j q) :=
    (peerDataArmsFromCoordinatesUniform_measurePreserving x j).measurable
  have hdata : MeasurableSet
      {q : RoundCoordinates p × (Player p.m → Arm p.K) |
        roundSlot q.1 = dataSlot} :=
    (measurableSet_singleton dataSlot).preimage hslot
  have hpeerSet : MeasurableSet
      {q : RoundCoordinates p × (Player p.m → Arm p.K) |
        ∀ i : Peer x j, peerDataArmsFromCoordinatesUniform x j q i ≠ a} := by
    exact (peerDataAvoidSet_measurable x j a).preimage hpeer
  exact hdata.inter hpeerSet

private def originalDataPeerEvent
    (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) (a : Arm p.K) :
    Set (RoundCoordinates p × (Player p.m → Arm p.K)) :=
  {q | roundSlot q.1 = dataSlot ∧
    ∀ i : Peer x j, peerDataArmsFromCoordinatesUniform x j q i ≠ a}

private theorem originalDataPeerEvent_mass_ge_eighth
    (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (a : Arm p.K) :
    ((roundCoordinatesMeasure p).prod (privateArmVectorMeasure p)).real
      (originalDataPeerEvent x j a) ≥ 1 / 8 := by
  let μ := currentSnapshotMeasure x t
  let projection : RoundCoordinates p × RoundPrivateValues x →
      RoundCoordinates p × (Player p.m → Arm p.K) := fun w => (w.1, w.2.1)
  have hprojection := currentSnapshot_coordinates_uniform_measurePreserving x t
  have hE := originalDataPeerEvent_measurable x j a
  have hevent :
      {w : RoundCoordinates p × RoundPrivateValues x |
        roundSlot w.1 = dataSlot ∧
          ∀ i : Peer x j, peerDataArms x j w i ≠ a} =
        projection ⁻¹' originalDataPeerEvent x j a := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, projection, originalDataPeerEvent]
    rw [peerDataArms_eq_coordinatesUniform]
  have hpre := hprojection.measureReal_preimage hE.nullMeasurableSet
  have hmass := peerData_release_data_mass x t j a ∅
  have hbase :
      μ.real {w : RoundCoordinates p × RoundPrivateValues x |
        roundSlot w.1 = dataSlot ∧
          ∀ i : Peer x j, peerDataArms x j w i ≠ a} =
        (1 / 2 : ℝ) * (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) := by
    simpa [forwardReleaseSet] using hmass
  have hpeer := peerDataAvoidance_mass_ge_quarter x t j a
  rw [peerDataAvoidance_mass] at hpeer
  calc
    ((roundCoordinatesMeasure p).prod (privateArmVectorMeasure p)).real
        (originalDataPeerEvent x j a) =
      μ.real {w : RoundCoordinates p × RoundPrivateValues x |
        roundSlot w.1 = dataSlot ∧
          ∀ i : Peer x j, peerDataArms x j w i ≠ a} := by
        calc
          _ = μ.real (projection ⁻¹' originalDataPeerEvent x j a) := hpre.symm
          _ = μ.real {w : RoundCoordinates p × RoundPrivateValues x |
              roundSlot w.1 = dataSlot ∧
                ∀ i : Peer x j, peerDataArms x j w i ≠ a} := by rw [← hevent]
    _ = (1 / 2 : ℝ) * (1 - 1 / (p.K : ℝ)) ^ (p.m - 2) := hbase
    _ ≥ (1 / 2 : ℝ) * (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hpeer (by norm_num)
    _ = 1 / 8 := by norm_num

private theorem coordinatorComplementEvent_measurable
    (x : BootstrapPhysicalBlock.Input p s) (a : Arm p.K) :
    MeasurableSet
      {c : BootstrapPhysicalBlock.AvoidArm p x.target | c.val ≠ a} :=
  MeasurableSet.of_discrete

private def coordinatorComplementEvent
    (x : BootstrapPhysicalBlock.Input p s) (a : Arm p.K) :
    Set (BootstrapPhysicalBlock.AvoidArm p x.target) :=
  {c | c.val ≠ a}

private theorem coordinatorComplementEvent_mass_ge_half
    (x : BootstrapPhysicalBlock.Input p s) (a z : Arm p.K)
    (htarget : x.target = z) (hza : z ≠ a) :
    (privateAvoidMeasure p x.target).real (coordinatorComplementEvent x a) ≥ 1 / 2 := by
  have hxt : x.target ≠ a := by simpa [htarget] using hza
  simpa [coordinatorComplementEvent] using
    privateAvoidMeasure_complement_ge_half p x.target a hxt

/-- A DATA row, every physical peer avoiding the held arm, and the original
coordinator complement draw avoiding it have their joint mass on the original
row/full-arm coordinates times the complement mass. -/
private theorem dataPeerCoordinatorComplement_mass_ge_sixteenth
    (x : BootstrapPhysicalBlock.Input p s) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (a z : Arm p.K)
    (htarget : x.target = z) (hza : z ≠ a) :
    (currentSnapshotMeasure x t).real
      {w : RoundCoordinates p × RoundPrivateValues x |
        (w.1, w.2.1) ∈ originalDataPeerEvent x j a ∧
          w.2.2.1 ∈ coordinatorComplementEvent x a} ≥ 1 / 16 := by
  have hE := originalDataPeerEvent_measurable x j a
  have hB := coordinatorComplementEvent_measurable x a
  have hfactor := currentSnapshot_event_coordinatorAvoid_mass x t
    (originalDataPeerEvent x j a) (coordinatorComplementEvent x a) hE hB
  have hEmass := originalDataPeerEvent_mass_ge_eighth x t j a
  have hBmass := coordinatorComplementEvent_mass_ge_half x a z htarget hza
  have hEmass_nonneg : (0 : ℝ) ≤
      ((roundCoordinatesMeasure p).prod (privateArmVectorMeasure p)).real
        (originalDataPeerEvent x j a) := by
    linarith
  calc
    (1 / 16 : ℝ) = (1 / 8 : ℝ) * (1 / 2 : ℝ) := by norm_num
    _ ≤ ((roundCoordinatesMeasure p).prod (privateArmVectorMeasure p)).real
          (originalDataPeerEvent x j a) *
        (privateAvoidMeasure p x.target).real (coordinatorComplementEvent x a) :=
      mul_le_mul hEmass hBmass (by norm_num)
        hEmass_nonneg
    _ = (currentSnapshotMeasure x t).real
        {w : RoundCoordinates p × RoundPrivateValues x |
          (w.1, w.2.1) ∈ originalDataPeerEvent x j a ∧
            w.2.2.1 ∈ coordinatorComplementEvent x a} := hfactor.symm

private theorem dataPeerCoordinatorComplement_subset_event
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (hactive : x.active j = true) (hid : x.ids (x.privateId j) t = false)
    (hchi : chi x t a = 1)
    (hmode : st.mode = .discover ∨ st.mode = .multicast) :
    {w : RoundCoordinates p × RoundPrivateValues x |
      (w.1, w.2.1) ∈ originalDataPeerEvent x j a ∧
        w.2.2.1 ∈ coordinatorComplementEvent x a} ⊆
      dataStayPositiveEvent x st t j a := by
  intro w hw
  rcases hw with ⟨⟨hdata, hpeer⟩, havoid⟩
  have hpeer' : ∀ i : Peer x j, peerDataArms x j w i ≠ a := by
    intro i
    rw [peerDataArms_eq_coordinatesUniform]
    exact hpeer i
  have havoid' : w.2.2.1.val ≠ a := by
    simpa [coordinatorComplementEvent] using havoid
  rcases hmode with hdiscover | hmulticast
  · simp [dataStayPositiveEvent, coordinatorSafeSet, hactive, hid, hchi,
      dataPeerAvoidEvent, peerDataAvoidSet, hdata, hpeer', hdiscover]
  · simp [dataStayPositiveEvent, coordinatorSafeSet, hactive, hid, hchi,
      dataPeerAvoidEvent, peerDataAvoidSet, hdata, hpeer', hmulticast,
      havoid']

/-- For every fixed snapshot input satisfying the explicit active-follower
isolation conditions, the existing `dataStayPositive` has mean at least the
source support indicator times the ID-zero indicator divided by sixteen. The
expectation is only under `currentSnapshotMeasure x t`. -/
theorem dataStayPositive_mean_ge
    (x : BootstrapPhysicalBlock.Input p s)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ x.uninformed}) (a z : Arm p.K)
    (_hcal : t ∈ calendarBlock p s)
    (hactive : x.active j = true) (hheld : x.held j = a)
    (htarget : x.target = z) (hza : z ≠ a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false)
    (hmode : st.mode = .discover ∨ st.mode = .multicast) :
    (∫ w : RoundCoordinates p × RoundPrivateValues x,
      dataStayPositive x st t j w.1 w.2 ∂currentSnapshotMeasure x t) ≥
      chi x t a * (if x.ids (x.privateId j) t = false then 1 else 0) / 16 := by
  have hmeas := dataStayPositive_measurable x st t j a z hheld
    htarget hza hinactive
  have hint := dataStayPositive_integrable x st t j a z hheld
    htarget hza hinactive
  have hnonneg : 0 ≤ᵐ[currentSnapshotMeasure x t]
      (fun w : RoundCoordinates p × RoundPrivateValues x =>
        dataStayPositive x st t j w.1 w.2) := by
    filter_upwards [] with w
    unfold dataStayPositive
    split_ifs <;> norm_num
  by_cases hid : x.ids (x.privateId j) t = false
  · have hchi0or1 : chi x t a = 0 ∨ chi x t a = 1 := by
      unfold chi
      split_ifs <;> simp
    rcases hchi0or1 with hchi0 | hchi1
    · simpa [hid, hchi0] using
        (integral_nonneg_of_ae hnonneg :
          0 ≤ ∫ w : RoundCoordinates p × RoundPrivateValues x,
            dataStayPositive x st t j w.1 w.2 ∂currentSnapshotMeasure x t)
    · let jointEvent : Set (RoundCoordinates p × RoundPrivateValues x) :=
        {w | (w.1, w.2.1) ∈ originalDataPeerEvent x j a ∧
          w.2.2.1 ∈ coordinatorComplementEvent x a}
      have hjointMeas : MeasurableSet jointEvent := by
        have htargetSet :=
          (originalDataPeerEvent_measurable x j a).prod
            (coordinatorComplementEvent_measurable x a)
        exact htargetSet.preimage
          (currentSnapshot_coordinates_uniform_coordinator_measurePreserving x t).measurable
      have hsubset := dataPeerCoordinatorComplement_subset_event x st t j a
        hactive hid hchi1 hmode
      have hpoint : ∀ w : RoundCoordinates p × RoundPrivateValues x,
          jointEvent.indicator (fun _ => (1 : ℝ)) w ≤
            dataStayPositive x st t j w.1 w.2 := by
        intro w
        by_cases hw : w ∈ jointEvent
        · have hevent : w ∈ dataStayPositiveEvent x st t j a := by
            exact hsubset (by simpa [jointEvent] using hw)
          have hpointEq := congrFun
            (dataStayPositive_eq_event_indicator x st t j a z hheld
              htarget hza hinactive) w
          rw [hpointEq]
          simp [jointEvent, hw, hevent]
        · have hvalue : 0 ≤ dataStayPositive x st t j w.1 w.2 := by
            unfold dataStayPositive
            split_ifs <;> norm_num
          simpa [Set.indicator, hw] using hvalue
      have hmono := integral_mono
        ((integrable_const (1 : ℝ)).indicator hjointMeas) hint hpoint
      have hmass := dataPeerCoordinatorComplement_mass_ge_sixteenth
        x t j a z htarget hza
      have hmean : (1 / 16 : ℝ) ≤
          ∫ w : RoundCoordinates p × RoundPrivateValues x,
            dataStayPositive x st t j w.1 w.2 ∂currentSnapshotMeasure x t := by
        calc
          (1 / 16 : ℝ) ≤ (currentSnapshotMeasure x t).real jointEvent := by
            simpa [jointEvent] using hmass
          _ = ∫ w : RoundCoordinates p × RoundPrivateValues x,
              jointEvent.indicator (fun _ => (1 : ℝ)) w ∂currentSnapshotMeasure x t := by
            rw [integral_indicator_const (1 : ℝ) hjointMeas, smul_eq_mul, mul_one]
          _ ≤ ∫ w : RoundCoordinates p × RoundPrivateValues x,
              dataStayPositive x st t j w.1 w.2 ∂currentSnapshotMeasure x t := hmono
      simpa [hid, hchi1] using hmean
  · simpa [hid] using
      (integral_nonneg_of_ae hnonneg :
        0 ≤ ∫ w : RoundCoordinates p × RoundPrivateValues x,
          dataStayPositive x st t j w.1 w.2 ∂currentSnapshotMeasure x t)

/-- Summing the fixed-snapshot means for an arbitrary supplied state at each
calendar time yields the sum of supported ID-zero rounds divided by sixteen.
This is a finite sum of the existing snapshot expectations, not an adaptive
block-law expectation. -/
theorem sum_dataStayPositive_mean_ge
    (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) (a : Arm p.K)
    (states : Fin p.T → BootstrapPhysicalBlock.State p)
    (hactive : x.active j = true) (hheld : x.held j = a)
    (hza : x.target ≠ a)
    (hinactive : ∀ k : {k // k ∈ x.uninformed}, k ≠ j → x.active k = false)
    (hmode : ∀ t ∈ calendarBlock p s,
      (states t).mode = .discover ∨ (states t).mode = .multicast) :
    (∑ t ∈ calendarBlock p s,
      ∫ w : RoundCoordinates p × RoundPrivateValues x,
        dataStayPositive x (states t) t j w.1 w.2 ∂currentSnapshotMeasure x t) ≥
      (∑ t ∈ calendarBlock p s,
        chi x t a * (if x.ids (x.privateId j) t = false then 1 else 0)) / 16 := by
  calc
    (∑ t ∈ calendarBlock p s,
      ∫ w : RoundCoordinates p × RoundPrivateValues x,
        dataStayPositive x (states t) t j w.1 w.2 ∂currentSnapshotMeasure x t) ≥
      ∑ t ∈ calendarBlock p s,
        chi x t a * (if x.ids (x.privateId j) t = false then 1 else 0) / 16 := by
      apply Finset.sum_le_sum
      intro t ht
      exact dataStayPositive_mean_ge x (states t) t j a x.target ht
        hactive hheld rfl hza hinactive (hmode t ht)
    _ = (∑ t ∈ calendarBlock p s,
        chi x t a * (if x.ids (x.privateId j) t = false then 1 else 0)) / 16 := by
      rw [Finset.sum_div]

/-- Literal actual-run specialization of the accepted stay-count comparison.
It concerns only the original input's executed run and bounds its counted
DATA stay-positive rounds by the existing all-slot `physicalStayGain`. -/
theorem actualRun_dataStayPositive_count_le_physicalStayGain
    (x : BootstrapPhysicalBlock.Input p s)
    (j : {j // j ∈ x.uninformed}) (hactive : x.active j = true) :
    ((calendarBlock p s).filter fun t =>
      dataStayPositive x (BootstrapPhysicalBlock.run x t.val) t j
        (roundCoordinates p t x.row)
        ((fun i => x.uniform i t),
          (x.coordinatorAvoid t, fun k => x.followerAvoid k t)) = 1).card ≤
      BootstrapPhysicalBlock.physicalStayGain x j :=
  dataStayPositive_count_le_physicalStayGain x j hactive

end Bandits.Support.BootstrapStayGainMean

end
