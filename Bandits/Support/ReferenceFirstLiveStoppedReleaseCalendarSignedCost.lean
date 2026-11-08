/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveStoppedReleaseWaiting
public import Bandits.Support.ReferenceFirstLivePhysicalSentinelCost
public import Bandits.Support.ReferenceFirstLiveInspectedFastCollision

/-!
# Calendar signed deficits on the actual stopped first release

Sources: `sources/zip4/manuscript/05_binary_transport.tex:293-348`,
`sources/zip4/manuscript/06_interruptions.tex:425-426,452-492`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`.

These internal readouts retain the actual physical records, whole reward table,
and signed deficits, including empty-pending gates and detecting rounds. They
make no conditional collision estimate or manuscript closure claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstLiveStoppedReleaseCalendarSignedCost

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

abbrev Source (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p

local notation "support" =>
  ReferenceFirstLiveSourceStoppedReleaseEndpoint.actualFirstReleaseSupport
    rate rewards C_star C_h
local notation "P" =>
  ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat
    rate rewards C_star C_h
local notation "Z" => ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge
  rate rewards C_star C_h
local notation "Rt" => ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards

/-- The signed physical deficit, masked only by actual stopped support and
analytical absence of a record or stored payload. -/
def signedStep (t : Fin p.T) (z : Source p) : ℝ :=
  if t.val + 1 ∈ support z then
    match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none => 0
    | some r =>
      match ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator with
      | none => 0
      | some M =>
        ReleaseRoundKernel.slowReward (Rt t) M.slowSet +
          (Rt t).val (r.actions (ActiveRoundActions.coordinator p.two_le_m)) -
          ∑ player : Fin p.m, ((r.ownEntries player).2).val.val
  else 0

/-- The actual reward-weighted sentinel charge on the same stopped support. -/
def stoppedSentinel (t : Fin p.T) (z : Source p) : ℝ :=
  if t.val + 1 ∈ support z then Z t z else 0

/-- The finite calendar sum retains negative deficits on empty-pending gates. -/
def totalSignedCost (z : Source p) : ℝ :=
  ∑ t : Fin p.T, signedStep rate rewards C_star C_h t z

private theorem actualRecord_fields (t : Fin p.T) (z : Source p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

private theorem record_coordinator_action
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (sel : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some sel) :
    r.actions (ActiveRoundActions.coordinator p.two_le_m) = sel.arm := by
  change r.output.preparation.arms.actions _ = _
  rw [ReferenceActivePhysicalStep.PreparedRound.action_coordinator]
  change ReferenceActivePhysicalStep.DispatchCut.arm r.output.preparation.coordinator = _
  simp only [ReferenceActivePhysicalStep.DispatchCut.arm, hsel]

private theorem pending_eq_record (t : Fin p.T) (z : Source p)
    (hSt : t.val + 1 ∈ support z)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (M : ReferenceActivePhysicalStep.Payload rate)
    (hM : ReferenceAssignmentPayloadPersistence.storedPayload
      r.input.state.coordinator = some M) :
    P t.val z = ReferencePhysicalReleaseQuota.pendingSet M r := by
  have ht := (actualRecord_fields rate rewards C_star C_h t z r hr).2.2.1
  have hg := (ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_gate_support_mem_iff_entry
    rate rewards C_star C_h z t).mp (Finset.mem_filter.mp hSt).1
  have hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z)
      t (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
    apply Option.some.inj
    simpa only [ReferenceSourcePrefixHistoryFiltration.entry,
      ReferenceSourcePrefixHistoryFiltration.incoming, hr, Option.map_some,
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry] using hg
  rw [ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_fin]
  simp only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.firstReleasePending, hSt,
    ite_true, ReferenceSourcePrefixHistoryFiltration.pending,
    ReferenceSourcePrefixHistoryFiltration.entry, ReferenceSourcePrefixHistoryFiltration.incoming,
    hr, Option.map_some, ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
    hgate, ite_true,
    ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
    ReferenceActivePhysicalStepMeasurability.decodeState_encodeState, hM,
    ReferenceRetainedReleasePhaseObservation.localReleasePending,
    Option.bind_some, Option.getD_some, ReferencePhysicalReleaseQuota.pendingSet, ht]

private theorem calendar_physical_payload (t : Fin p.T) (z : Source p)
    (hSt : t.val + 1 ∈ support z) :
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (sel : ReferenceActivePhysicalStep.Selection r.input),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      r.output.preparation.coordinator.selection = some sel ∧
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator =
        some sel.view.payload ∧
      sel.view.pendingAtChoice = ∅ ∧
      sel.view.payload.sigma.val =
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z ∧
      ReleaseRoundKernel.slowReward (Rt t) sel.view.payload.slowSet + (Rt t).val sel.arm -
          (∑ player : Fin p.m, ((r.ownEntries player).2).val.val) ≤
        (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet sel.view.payload r,
          ReleaseRoundKernel.chi (Rt t) (sel.view.payload.assignment.assigned i)) +
        ReferenceFirstLiveFastCollisionSection.recordFastCollisionCharge sel.view.payload r := by
  have hentry := (ReferenceFirstLiveSourceStoppedReleaseEndpoint.actual_gate_support_mem_iff_entry
    rate rewards C_star C_h z t).mp (Finset.mem_filter.mp hSt).1
  have hby : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z := by
    by_contra hn
    have hnrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hn
    simp only [ReferenceSourcePrefixHistoryFiltration.entry,
      ReferenceSourcePrefixHistoryFiltration.incoming, hnrec, Option.map_none] at hentry
    cases hentry
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed
  have hs : s ≤ t.val := hby.2
  have hstart : ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
      rate rewards C_star C_h z = s := rfl
  rw [hstart] at hentry
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome =
        true := hby.1
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed
    rate z rewards C_star C_h hcross
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hcross
  have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart initial s :=
    (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
      rate z rewards C_star C_h hcross).2.1
  have hspan : s + (p.T - s) ≤ p.T := by have ht := t.isLt; omega
  have hj : t.val - s < p.T - s := by have ht := t.isLt; omega
  let run := ReferenceLocalReleaseGateChronology.sourceRun
    rate z rewards C_star C_h hcross s (p.T - s) rfl hspan
  let r := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (t.val - s)
    (by have ht := t.isLt; omega) hactive
  have hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r :=
    ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t z initial hlaunch hs
  have htime : r.input.time = t := (actualRecord_fields rate rewards C_star C_h t z r hr).2.2.1
  have hrec : run.records[t.val - s]'(by
      simp only [run, ReferenceLocalReleaseGateChronology.sourceRun,
        ReferenceActivePhysicalHorizon.run_record_count]
      exact hj) = r :=
    ReferenceLocalReleaseGateChronology.run_record_at initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hactive
      (p.T - s) hspan ⟨t.val - s, hj⟩
  have hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s r.input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
    apply Option.some.inj
    simpa only [ReferenceSourcePrefixHistoryFiltration.entry,
      ReferenceSourcePrefixHistoryFiltration.incoming, hr, Option.map_some,
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry, htime] using hentry
  have hgateRun : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s
      (run.records[t.val - s]'(by
        simp only [run, ReferenceLocalReleaseGateChronology.sourceRun,
          ReferenceActivePhysicalHorizon.run_record_count]
        exact hj)).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState
        (run.records[t.val - s]'(by
          simp only [run, ReferenceLocalReleaseGateChronology.sourceRun,
            ReferenceActivePhysicalHorizon.run_record_count]
          exact hj)).input.state) = true := by rw [hrec]; exact hgate
  have hbound := ReferenceFirstLivePhysicalSentinelCost.actual_first_live_gate_sentinel_cost_bound
    rate z rewards C_star C_h (p.T - s) hcross hspan ⟨t.val - s, hj⟩ hgateRun
  have hselected := ReferenceFirstLiveSourceReleaseSupport.actual_first_live_gate_selected_empty
    (rate := rate) z rewards C_star C_h (p.T - s) hspan hcross ⟨t.val - s, hj⟩ hgateRun
  dsimp only at hbound hselected
  rw [hrec] at hbound hselected
  obtain ⟨sel, hsel, hstored, hempty, hbound⟩ := hbound
  obtain ⟨sel', hsel', M, hM, _hempty', hsigma⟩ := hselected
  have heq : sel' = sel := Option.some.inj (hsel'.symm.trans hsel)
  subst sel'
  have haction := record_coordinator_action rate r sel hsel
  refine ⟨r, sel, hr, hsel, hstored, hempty, ?_, ?_⟩
  · rw [hM]
    exact hsigma
  · simpa only [ReferenceFirstLiveFastCollisionSection.recordFastCollisionCharge,
      haction, (actualRecord_fields rate rewards C_star C_h t z r hr).2.2.2,
      htime] using hbound

variable (control0 : ContinuousLearningRows.TimeControl p)

private theorem assigned_zero_off_guard
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : Fin (t.val + 1)) (z : Source p)
    (hg : z ∉ ReferenceFirstLiveSourceStoppedReleaseService.g
      rate rewards C_star C_h control0 i t q s) :
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
      rate rewards C_star C_h control0 i t q s.val
      (Nat.le_of_lt_succ s.isLt) s.val z = 0 := by
  dsimp only [ReferenceFirstLiveSourceStoppedReleaseService.g] at hg
  simp only [ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi,
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues,
    dite_eq_right hg, ReferenceFirstLiveInspectedCoefficients.zeroValues]

private theorem assigned_sum_on_guard
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : Fin (t.val + 1)) (z : Source p)
    (hg : z ∈ ReferenceFirstLiveSourceStoppedReleaseService.g
      rate rewards C_star C_h control0 i t q s) :
    ReferenceFirstLiveSourceStoppedReleaseService.c rate rewards C_star C_h control0 i t z =
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
        rate rewards C_star C_h control0 i t q s.val
        (Nat.le_of_lt_succ s.isLt) s.val z := by
  unfold ReferenceFirstLiveSourceStoppedReleaseService.c
  rw [Finset.sum_eq_single q]
  · apply Finset.sum_eq_single s
    · intro s' _hne hs'
      apply assigned_zero_off_guard rate rewards C_star C_h control0
      intro hg'
      exact hs' (ReferenceFirstLiveSourceStoppedReleaseService.guard_strata_exclusive
        rate rewards C_star C_h control0 i i t q q s s' z hg hg').2.symm
    · intro hn
      exact (hn (Finset.mem_univ _)).elim
  · intro q' _hne hq'
    apply Finset.sum_eq_zero
    intro s' _hs'
    apply assigned_zero_off_guard rate rewards C_star C_h control0
    intro hg'
    exact hq' (ReferenceFirstLiveSourceStoppedReleaseService.guard_strata_exclusive
      rate rewards C_star C_h control0 i i t q q' s s' z hg hg').1.symm
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

private theorem assigned_coefficient_on_record
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p)
    (hi : i ∈ P t.val z)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (M : ReferenceActivePhysicalStep.Payload rate)
    (hM : ReferenceAssignmentPayloadPersistence.storedPayload
      r.input.state.coordinator = some M) :
    ReferenceFirstLiveSourceStoppedReleaseService.c rate rewards C_star C_h control0 i t z =
      ReleaseRoundKernel.chi (Rt t) (M.assignment.assigned i) := by
  obtain ⟨⟨q, s⟩, hg, _hunique⟩ :=
    ReferenceFirstLiveSourceStoppedReleaseService.pending_guard_coverage
      rate rewards C_star C_h control0 i t z hi
  rw [assigned_sum_on_guard rate rewards C_star C_h control0 i t q s z hg]
  have hfields := ReferenceFirstLiveInspectedGuardReadout.baseline_fields_eq_incoming
    rate rewards C_star C_h control0 i t q s.val (Nat.le_of_lt_succ s.isLt) s.val z hg
  dsimp only at hfields
  obtain ⟨code, payload, live, hin, hcode, _hdecoded, _htime,
      hpayload, _hweights, _htimeAt, _hpending, _hprior, _hcutoff, _hvalid, _hframe⟩ := hfields
  have hcodeEq : ReferenceActivePhysicalStepMeasurability.encodeState r.input.state = code := by
    simpa only [ReferenceSourcePrefixHistoryFiltration.incoming, hr,
      Option.map_some, Option.some.injEq] using hin
  have hstored : ReferenceRetainedReleasePhaseObservation.localStoredPayload code = some M := by
    rw [← hcodeEq, ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState, hM]
  have hpayloadM : payload = M := by
    simpa only [ReferenceRetainedReleasePhaseObservation.localStoredPayload,
      hcode, Option.some.injEq] using hstored
  dsimp only [ReferenceFirstLiveSourceStoppedReleaseService.g] at hg
  simp only [ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi,
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues,
    dite_eq_left hg]
  rw [hpayload, hpayloadM]

/-- Calendar support determines the same actual record, selection and payload,
with its original rows, selected index, time and whole rewards. The coefficient
identity is restricted to actual pending followers; the sentinel retains the
physical auxiliary reward. -/
theorem actual_first_release_calendar_payload (t : Fin p.T) (z : Source p)
    (hSt : t.val + 1 ∈ support z) :
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (sel : ReferenceActivePhysicalStep.Selection r.input),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards ∧
      r.output.preparation.coordinator.selection = some sel ∧
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator =
        some sel.view.payload ∧
      sel.view.pendingAtChoice = ∅ ∧
      sel.view.payload.sigma.val =
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart rate rewards C_star C_h z ∧
      r.actions (ActiveRoundActions.coordinator p.two_le_m) = sel.arm ∧
      P t.val z = ReferencePhysicalReleaseQuota.pendingSet sel.view.payload r ∧
      (∀ i ∈ P t.val z,
        ReferenceFirstLiveSourceStoppedReleaseService.c rate rewards C_star C_h control0 i t z =
          ReleaseRoundKernel.chi (Rt t) (sel.view.payload.assignment.assigned i)) ∧
      Z t z = ReferenceFirstLiveFastCollisionSection.recordFastCollisionCharge sel.view.payload r := by
  obtain ⟨r, sel, hr, hsel, hstored, hempty, hsigma, _hbound⟩ :=
    calendar_physical_payload rate rewards C_star C_h t z hSt
  obtain ⟨hrows, hJ, htime, hrewards⟩ := actualRecord_fields rate rewards C_star C_h t z r hr
  refine ⟨r, sel, hr, hrows, hJ, htime, hrewards, hsel, hstored, hempty, hsigma,
    record_coordinator_action rate r sel hsel,
    pending_eq_record rate rewards C_star C_h t z hSt r hr sel.view.payload hstored, ?_, ?_⟩
  · intro i hi
    exact assigned_coefficient_on_record rate rewards C_star C_h control0
      i t z hi r hr sel.view.payload hstored
  · simp only [ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge, hr, hstored]

private theorem pending_empty_off_support (t : Fin p.T) (z : Source p)
    (hSt : t.val + 1 ∉ support z) : P t.val z = ∅ := by
  rw [ReferenceFirstLiveSourceStoppedReleaseQuota.firstReleasePendingNat_fin]
  exact ite_eq_right hSt

/-- The stopped reward-weighted sentinel equals its actual pending mask.
This does not identify the physical reward with its positivity indicator. -/
theorem stoppedSentinel_eq_pending_mask (t : Fin p.T) (z : Source p) :
    stoppedSentinel rate rewards C_star C_h t z =
      (if (P t.val z).Nonempty then (1 : ℝ) else 0) * Z t z := by
  by_cases hSt : t.val + 1 ∈ support z
  · obtain ⟨r, sel, hr, _hsel, hstored, _hempty, _hsigma, _hbound⟩ :=
      calendar_physical_payload rate rewards C_star C_h t z hSt
    have hP := pending_eq_record rate rewards C_star C_h t z hSt r hr sel.view.payload hstored
    have hZ : Z t z =
        ReferenceFirstLiveFastCollisionSection.recordFastCollisionCharge sel.view.payload r := by
      simp only [ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge, hr, hstored]
    by_cases hp : (P t.val z).Nonempty
    · simp only [stoppedSentinel, hSt, ite_true, hp, one_mul]
    · have hzero : Z t z = 0 := by
        rw [hZ]
        simp only [ReferenceFirstLiveFastCollisionSection.recordFastCollisionCharge,
          ← hP, hp, and_false, ite_false]
      simp only [stoppedSentinel, hSt, ite_true, hp, ite_false, hzero, mul_zero]
  · have hP := pending_empty_off_support rate rewards C_star C_h t z hSt
    simp only [stoppedSentinel, hSt, ite_false, hP, Finset.not_nonempty_empty, zero_mul]

/-- The deterministic signed-deficit inequality on the entire source carrier.
An active gate with no pending follower still contributes its signed deficit. -/
theorem actual_first_release_calendar_signed_bound (t : Fin p.T) (z : Source p) :
    signedStep rate rewards C_star C_h t z ≤
        (∑ i ∈ P t.val z,
          ReferenceFirstLiveSourceStoppedReleaseService.firstReleaseAssignedChi
            rate rewards C_star C_h control0 i t.val z) +
        stoppedSentinel rate rewards C_star C_h t z ∧
      stoppedSentinel rate rewards C_star C_h t z =
        (if (P t.val z).Nonempty then (1 : ℝ) else 0) * Z t z := by
  refine ⟨?_, stoppedSentinel_eq_pending_mask rate rewards C_star C_h t z⟩
  by_cases hSt : t.val + 1 ∈ support z
  · obtain ⟨r, sel, hr, hsel, hstored, _hempty, _hsigma, hbound⟩ :=
      calendar_physical_payload rate rewards C_star C_h t z hSt
    have hP := pending_eq_record rate rewards C_star C_h t z hSt r hr sel.view.payload hstored
    have haction := record_coordinator_action rate r sel hsel
    have hsum : (∑ i ∈ P t.val z,
        ReferenceFirstLiveSourceStoppedReleaseService.firstReleaseAssignedChi
          rate rewards C_star C_h control0 i t.val z) =
        ∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet sel.view.payload r,
          ReleaseRoundKernel.chi (Rt t) (sel.view.payload.assignment.assigned i) := by
      rw [← hP]
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [ReferenceFirstLiveSourceStoppedReleaseService.firstReleaseAssignedChi,
        dite_eq_left t.isLt, Fin.eta] using
          assigned_coefficient_on_record rate rewards C_star C_h control0
            i t z hi r hr sel.view.payload hstored
    simpa only [signedStep, stoppedSentinel, hSt, ite_true, hr, hstored, haction, hsum,
      ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge] using hbound
  · simp only [signedStep, stoppedSentinel, hSt, ite_false,
      pending_empty_off_support rate rewards C_star C_h t z hSt, Finset.sum_empty, zero_add,
      le_refl]

/-- With no stopped gate, the whole signed calendar sum is zero. -/
theorem totalSignedCost_eq_zero_of_support_empty (z : Source p)
    (h : support z = ∅) : totalSignedCost rate rewards C_star C_h z = 0 := by
  simp only [totalSignedCost, signedStep, h, Finset.notMem_empty, ite_false, Finset.sum_const_zero]

include control0 in
/-- Empty pending sets remove the upper-bound charges, while the original
signed deficit remains in the calendar sum. No empty-gate premise is used. -/
theorem signedStep_nonpos_of_pending_empty (t : Fin p.T) (z : Source p)
    (hP : P t.val z = ∅) : signedStep rate rewards C_star C_h t z ≤ 0 := by
  have h := (actual_first_release_calendar_signed_bound
    rate rewards C_star C_h control0 t z).1
  rw [stoppedSentinel_eq_pending_mask rate rewards C_star C_h t z, hP] at h
  simpa only [Finset.sum_empty, Finset.not_nonempty_empty, ite_false, zero_mul, zero_add] using h

private theorem measurable_optionElim {α β X : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace X]
    (f : α × X → β) (hf : Measurable f) (g : X → β) (hg : Measurable g)
    (v : X → Option α) (hv : Measurable v) :
    Measurable (fun x => match v x with | none => g x | some a => f (a, x)) := by
  have h := (hf.sumElim (hg.comp measurable_snd)).comp
    (MeasurableEquiv.sumProdDistrib α PUnit X).measurable_toFun
  have hpair := h.comp
    (((comap_measurable (Equiv.optionEquivSumPUnit α)).comp hv).prodMk measurable_id)
  convert hpair using 1
  funext x
  change (match v x with | none => g x | some a => f (a, x)) =
    Sum.elim f (g ∘ Prod.snd) ((Equiv.sumProdDistrib α PUnit X)
      ((Equiv.optionEquivSumPUnit α) (v x), x))
  cases v x <;> rfl

private def codeSignedDeficit (t : Fin p.T)
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) : ℝ :=
  match ReferenceRetainedReleasePhaseObservation.localStoredPayload code.2.1 with
  | none => 0
  | some M =>
    ReleaseRoundKernel.slowReward (Rt t) M.slowSet +
      (Rt t).val (ReferenceActiveHorizonMeasurability.roundRecordCodeActions code
        (ActiveRoundActions.coordinator p.two_le_m)) -
      ∑ player : Fin p.m,
        ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code player).2).val.val

private theorem measurable_codeSignedDeficit (t : Fin p.T) :
    Measurable (codeSignedDeficit rate rewards t) := by
  let Code := ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)
  have hslow : Measurable (fun M : ReferenceActivePhysicalStep.Payload rate => M.slowSet.val) := by
    change Measurable (fun M : ReferenceActivePhysicalStep.Payload rate =>
      (LaterAssignmentStartMeasurability.payloadObservation M).2.2.1)
    exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable _)))
  have hslowReward : Measurable (fun M : ReferenceActivePhysicalStep.Payload rate =>
      ReleaseRoundKernel.slowReward (Rt t) M.slowSet) :=
    (measurable_of_countable (fun U : Finset (Fin p.K) => ∑ a ∈ U, (Rt t).val a)).comp hslow
  have haction : Measurable (fun code : Code =>
      ReferenceActiveHorizonMeasurability.roundRecordCodeActions code
        (ActiveRoundActions.coordinator p.two_le_m)) := by
    exact (ReferenceActiveHorizonMeasurability.measurable_roundRecordCodeOwnEntry
      (ActiveRoundActions.coordinator p.two_le_m)).fst
  have hreward : Measurable (fun code : Code =>
      (Rt t).val (ReferenceActiveHorizonMeasurability.roundRecordCodeActions code
        (ActiveRoundActions.coordinator p.two_le_m))) :=
    (measurable_of_countable _).comp haction
  have hown (player : Fin p.m) : Measurable (fun code : Code =>
      ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code player).2).val.val) :=
    (ReferenceActiveHorizonMeasurability.measurable_roundRecordCodeOwnEntry player).snd.subtype_val.subtype_val
  have hsum : Measurable (fun code : Code => ∑ player : Fin p.m,
      ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code player).2).val.val) :=
    Finset.measurable_fun_sum _ (fun player _ => hown player)
  have h := measurable_optionElim
    (fun v : ReferenceActivePhysicalStep.Payload rate × Code =>
      ReleaseRoundKernel.slowReward (Rt t) v.1.slowSet +
        (Rt t).val (ReferenceActiveHorizonMeasurability.roundRecordCodeActions v.2
          (ActiveRoundActions.coordinator p.two_le_m)) -
        ∑ player : Fin p.m,
          ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry v.2 player).2).val.val)
    (((hslowReward.comp measurable_fst).add (hreward.comp measurable_snd)).sub
      (hsum.comp measurable_snd))
    (fun _ => (0 : ℝ)) measurable_const _
    ((ReferenceReleaseStrictPastFactor.measurable_localStoredPayload rate).comp
      (measurable_fst.comp measurable_snd))
  convert h using 1
  funext code
  dsimp only [Function.comp_apply, codeSignedDeficit]
  cases ReferenceRetainedReleasePhaseObservation.localStoredPayload code.2.1 <;> rfl

private theorem codeSignedDeficit_record (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    codeSignedDeficit rate rewards t (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
      match ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator with
      | none => 0
      | some M =>
        ReleaseRoundKernel.slowReward (Rt t) M.slowSet +
          (Rt t).val (r.actions (ActiveRoundActions.coordinator p.two_le_m)) -
          ∑ player : Fin p.m, ((r.ownEntries player).2).val.val := by
  have hstored : ReferenceRetainedReleasePhaseObservation.localStoredPayload
      (ReferenceActiveHorizonMeasurability.roundRecordCode r).2.1 =
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator := by
    rw [ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
      (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r).1]
  simp only [codeSignedDeficit, hstored,
    (ReferenceActiveHorizonMeasurability.roundRecordCode_front r).2.2.1,
    (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r).2.2.2.2]
  rfl

include control0 in
/-- Ambient Borel measurability on the original continuous source carrier. -/
theorem signedStep_measurable (t : Fin p.T) :
    Measurable (signedStep rate rewards C_star C_h t) := by
  classical
  have h := measurable_optionElim
    (fun v : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) ×
      Source p => codeSignedDeficit rate rewards t v.1)
    ((measurable_codeSignedDeficit rate rewards t).comp measurable_fst)
    (fun _ => (0 : ℝ)) measurable_const _
    (ReferenceFirstLiveInspectedFastCollision.measurable_actualRecordCode rate rewards C_star C_h t)
  have hsupport : MeasurableSet {z : Source p | t.val + 1 ∈ support z} :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le _ _
      (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_support_adapted
        rate rewards C_star C_h control0 t)
  have hreadout : Measurable (fun z : Source p =>
      match ReferenceFirstLiveInspectedFastCollision.actualRecordCode
          rate rewards C_star C_h t z with
      | none => (0 : ℝ)
      | some code => codeSignedDeficit rate rewards t code) := by
    convert h using 1
    funext z
    cases ReferenceFirstLiveInspectedFastCollision.actualRecordCode
      rate rewards C_star C_h t z <;> rfl
  have hm : Measurable (fun z : Source p =>
      if t.val + 1 ∈ support z then
        match ReferenceFirstLiveInspectedFastCollision.actualRecordCode
            rate rewards C_star C_h t z with
        | none => 0
        | some code => codeSignedDeficit rate rewards t code
      else (0 : ℝ)) := hreadout.ite hsupport measurable_const
  convert hm using 1
  funext z
  unfold signedStep
  split_ifs with hSt
  · cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z with
    | none => simp only [ReferenceFirstLiveInspectedFastCollision.actualRecordCode,
        hr, Option.map_none]
    | some r =>
      simp only [ReferenceFirstLiveInspectedFastCollision.actualRecordCode, hr, Option.map_some]
      exact (codeSignedDeficit_record rate rewards t r).symm
  · rfl

include control0 in
/-- Ambient Borel measurability of the reward-weighted stopped sentinel. -/
theorem stoppedSentinel_measurable (t : Fin p.T) :
    Measurable (stoppedSentinel rate rewards C_star C_h t) := by
  have hsupport : MeasurableSet {z : Source p | t.val + 1 ∈ support z} :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le _ _
      (ReferenceFirstLiveSourceStoppedReleaseAdaptation.first_release_support_adapted
        rate rewards C_star C_h control0 t)
  exact (ReferenceFirstLiveInspectedFastCollision.sourceFastCollisionCharge_measurable
    rate rewards C_star C_h t).ite hsupport measurable_const

include control0 in
/-- The entire signed calendar sum is Borel. -/
theorem totalSignedCost_measurable :
    Measurable (totalSignedCost rate rewards C_star C_h) :=
  Finset.measurable_fun_sum _ (fun t _ => signedStep_measurable rate rewards C_star C_h control0 t)

/-- Typed rewards and own observations give a uniform absolute bound without
any score, queue, successor-success or pending premise. -/
theorem signedStep_abs_le (t : Fin p.T) (z : Source p) :
    |signedStep rate rewards C_star C_h t z| ≤ (p.m : ℝ) := by
  have hm : (0 : ℝ) ≤ p.m := Nat.cast_nonneg _
  unfold signedStep
  split_ifs
  · cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z with
    | none => simpa only [abs_zero] using hm
    | some r =>
      dsimp only
      cases hM : ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator with
      | none => simpa only [abs_zero] using hm
      | some M =>
        change |ReleaseRoundKernel.slowReward (Rt t) M.slowSet +
          (Rt t).val (r.actions (ActiveRoundActions.coordinator p.two_le_m)) -
          ∑ player : Fin p.m, ((r.ownEntries player).2).val.val| ≤ (p.m : ℝ)
        have hslow0 : 0 ≤ ReleaseRoundKernel.slowReward (Rt t) M.slowSet :=
          Finset.sum_nonneg (fun a _ => ((Rt t).property a).1)
        have hslow1 : ReleaseRoundKernel.slowReward (Rt t) M.slowSet ≤
            (M.slowSet.val.card : ℝ) := by
          calc
            _ ≤ ∑ _a ∈ M.slowSet.val, (1 : ℝ) :=
              Finset.sum_le_sum (fun a _ => ((Rt t).property a).2)
            _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        have hcard : (M.slowSet.val.card : ℝ) + 1 = p.m := by
          exact_mod_cast CanonicalOrientedSetLaw.slowSet_card p.two_le_m M.slowSet
        have haction := (Rt t).property (r.actions (ActiveRoundActions.coordinator p.two_le_m))
        have hobs0 : 0 ≤ ∑ player : Fin p.m, ((r.ownEntries player).2).val.val :=
          Finset.sum_nonneg (fun player _ => (r.ownEntries player).2.val.property.1)
        have hobs1 : (∑ player : Fin p.m, ((r.ownEntries player).2).val.val) ≤ (p.m : ℝ) := by
          calc
            _ ≤ ∑ _player : Fin p.m, (1 : ℝ) :=
              Finset.sum_le_sum (fun player _ => (r.ownEntries player).2.val.property.2)
            _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, mul_one]
        exact abs_le.mpr ⟨by linarith only [hslow0, haction.1, hobs1],
          by linarith only [hslow1, hcard, haction.2, hobs0]⟩
  · simpa only [abs_zero] using hm

/-- The absolute total signed cost is at most the horizon times the player count. -/
theorem totalSignedCost_abs_le (z : Source p) :
    |totalSignedCost rate rewards C_star C_h z| ≤ (p.T : ℝ) * (p.m : ℝ) := by
  calc
    _ ≤ ∑ t : Fin p.T, |signedStep rate rewards C_star C_h t z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin p.T, (p.m : ℝ) :=
      Finset.sum_le_sum (fun t _ => signedStep_abs_le rate rewards C_star C_h t z)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem stoppedSentinel_bounds (t : Fin p.T) (z : Source p) :
    0 ≤ stoppedSentinel rate rewards C_star C_h t z ∧
      stoppedSentinel rate rewards C_star C_h t z ≤ 1 := by
  unfold stoppedSentinel
  split_ifs
  · exact ReferenceFirstLiveInspectedFastCollision.sourceFastCollisionCharge_bounds
      rate rewards C_star C_h t z
  · exact ⟨le_rfl, zero_le_one⟩

include control0 in
/-- Integrability under the same original source law, without normalization. -/
theorem signedStep_integrable (t : Fin p.T) :
    Integrable (signedStep rate rewards C_star C_h t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let : IsProbabilityMeasure (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  exact (integrable_const (p.m : ℝ)).mono'
    (signedStep_measurable rate rewards C_star C_h control0 t).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs] using signedStep_abs_le rate rewards C_star C_h t z))

include control0 in
theorem stoppedSentinel_integrable (t : Fin p.T) :
    Integrable (stoppedSentinel rate rewards C_star C_h t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let : IsProbabilityMeasure (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  exact (integrable_const (1 : ℝ)).mono'
    (stoppedSentinel_measurable rate rewards C_star C_h control0 t).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (stoppedSentinel_bounds rate rewards C_star C_h t z).1]
      exact (stoppedSentinel_bounds rate rewards C_star C_h t z).2))

include control0 in
/-- Integrability of the complete signed calendar sum on the original law. -/
theorem totalSignedCost_integrable :
    Integrable (totalSignedCost rate rewards C_star C_h)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
  integrable_finsetSum _ (fun t _ => signedStep_integrable rate rewards C_star C_h control0 t)

end Bandits.Support.ReferenceFirstLiveStoppedReleaseCalendarSignedCost
