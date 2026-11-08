/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAwaitedWaitingCost

/-!
# First issued collection-cutoff history

This module records the pre-choice `initializeAt` command issued by the
actual live coordinator clock.  Its first date is kept distinct from the
first chosen cutoff and from the initial assignment launch. The unchanged
awaited waiting charge has its `Bcol` bound at this earlier stopped field under
the original source-input law. The intended consumer is first-collection
stopped-charge domination and transfer assembly. Source collection-calendar
coverage, decoder coverage, and a genuine physical stop remain separate work.

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-14,40-62,425-431,459-487`
and `sources/zip4/manuscript/05_binary_transport.tex:180-240`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams
open ReferenceSourcePrefixHistoryFiltration
open PhaseStartConditionalWaiting
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstCollectionAwaitedCutoffHistory

variable {p : ConstructorDimensions.Parameters}

/-- The actual pre-choice live-clock request to initialize collection at this
calendar round.  It is read from the unchanged prior clock and pending set in
the actual incoming coordinator register. -/
def issuedAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  ∃ r, actualRecord rate rewards C_star C_h t z = some r ∧
    ∃ reg owned base,
      r.input.state.coordinator = .live reg owned base ∧
      ∃ out,
        CoordinatorPhaseClock.startRound p rate.eta.val t reg.priorClock
          reg.pendingAtChoice = .ok out ∧
        out.ledgerCommand = some (.initializeAt t)

/-- Calendar indices at which the actual pre-choice collection command was
issued. -/
def issuedDateIndices
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin p.T) :=
  Finset.univ.filter fun t => issuedAt rate rewards C_star C_h t z

/-- The clock query read from the existing countable live-register code. -/
def issuedLiveCode
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (t : Fin p.T)
    (code : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) : Bool :=
  decide (∃ out,
    CoordinatorPhaseClock.startRound p rate.eta.val t
      ⟨code.clockSigma, code.clockCutoff, code.clockBoundary, code.clockProposal⟩
      code.pending = .ok out ∧
    out.ledgerCommand = some (.initializeAt t))

/-- Read the query only from the live tag and its discrete clock coordinates;
the complete payload in the original coordinator code is left untouched. -/
def issuedCoordinatorCode
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (t : Fin p.T)
    (code : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate) : Bool :=
  match code with
  | .inr (.inl (_, live)) => issuedLiveCode rate t live
  | _ => false

/-- The same countable-coordinate query lifted to the lossless complete state
code. -/
def issuedStateCode
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (t : Fin p.T)
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate) : Bool :=
  issuedCoordinatorCode rate t code.1

/-- The measurable incoming-code query; absent records remain false. -/
def issuedIncomingCode
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (t : Fin p.T)
    (code : Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate)) : Bool :=
  (code.map (issuedStateCode rate t)).getD false

/-- The clock query is measurable on the already discrete live coordinates. -/
theorem measurable_issuedLiveCode
    (rate : ReferenceActivePhysicalStep.RateInput p) (t : Fin p.T) :
    Measurable (issuedLiveCode rate t) := by
  exact measurable_of_countable _

theorem measurable_issuedCoordinatorCode
    (rate : ReferenceActivePhysicalStep.RateInput p) (t : Fin p.T) :
    Measurable (issuedCoordinatorCode rate t) := by
  change Measurable
    (Sum.elim (fun _ : Unit => false)
      (Sum.elim
        (fun x : ReferenceActivePhysicalStep.Payload rate ×
          ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
            issuedLiveCode rate t x.2)
        (fun _ : (ReferenceActivePhysicalStep.Payload rate ×
          (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit =>
            false)))
  exact Measurable.sumElim measurable_const
    (Measurable.sumElim
      ((measurable_issuedLiveCode rate t).comp measurable_snd) measurable_const)

theorem measurable_issuedStateCode
    (rate : ReferenceActivePhysicalStep.RateInput p) (t : Fin p.T) :
    Measurable (issuedStateCode rate t) := by
  exact (measurable_issuedCoordinatorCode rate t).comp measurable_fst

theorem measurable_issuedIncomingCode
    (rate : ReferenceActivePhysicalStep.RateInput p) (t : Fin p.T) :
    Measurable (issuedIncomingCode rate t) := by
  let f : ReferenceActivePhysicalStepMeasurability.StateCode p rate → Bool :=
    issuedStateCode rate t
  have hf : Measurable f := measurable_issuedStateCode rate t
  have hmap : Measurable (fun code : Option
      (ReferenceActivePhysicalStepMeasurability.StateCode p rate) => code.map f) := by
    exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun pair : ReferenceActivePhysicalStepMeasurability.StateCode p rate ×
        Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate) => f pair.1)
      (hf.comp measurable_fst)
      (fun code : Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate) => code)
      measurable_id
  have hget : Measurable (fun code : Option Bool => code.getD false) :=
    let e : Option Bool ≃ᵐ Bool ⊕ PUnit := {
      toEquiv := Equiv.optionEquivSumPUnit Bool
      measurable_toFun := comap_measurable _
      measurable_invFun := by
        apply measurable_comap_iff.mpr
        exact measurable_id }
    let hcomp : Measurable
        (fun code : Bool ⊕ PUnit => (e.symm code).getD false) := by
      apply measurable_fun_sum
      · convert measurable_id using 1
        ext b
        simp [e]
      · convert (measurable_const : Measurable (fun _ : PUnit => false)) using 1
        ext u
        simp [e]
    e.symm.measurable_comp_iff.mp hcomp
  exact hget.comp hmap

/-- The code query is exactly the literal record-and-command predicate. -/
theorem issuedAt_iff_incoming_code_query
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    issuedAt rate rewards C_star C_h t z ↔
      issuedIncomingCode rate t
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z) = true := by
  classical
  cases hrecord : actualRecord rate rewards C_star C_h t z with
  | none =>
      simp [issuedAt, issuedIncomingCode,
        ReferenceSourcePrefixHistoryFiltration.incoming, hrecord]
  | some r =>
      cases hcoord : r.input.state.coordinator with
      | first =>
          simp [issuedAt, issuedIncomingCode, issuedStateCode, issuedCoordinatorCode,
            ReferenceSourcePrefixHistoryFiltration.incoming, hrecord, hcoord,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
      | dagger =>
          simp [issuedAt, issuedIncomingCode, issuedStateCode, issuedCoordinatorCode,
            ReferenceSourcePrefixHistoryFiltration.incoming, hrecord, hcoord,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
      | collection payload ledger proposal =>
          simp [issuedAt, issuedIncomingCode, issuedStateCode, issuedCoordinatorCode,
            ReferenceSourcePrefixHistoryFiltration.incoming, hrecord, hcoord,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
      | live reg owned base =>
          simp [issuedAt, issuedIncomingCode, issuedStateCode, issuedCoordinatorCode,
            issuedLiveCode, ReferenceSourcePrefixHistoryFiltration.incoming,
            hrecord, hcoord, ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            ReferenceActivePhysicalStepMeasurability.encodeLive]

/-- Predictability of the actual pre-choice command at the original
source-prefix history boundary. -/
theorem issuedAt_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
        (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        issuedAt rate rewards C_star C_h t z} := by
  have hquery := (measurable_issuedIncomingCode rate t).comp
    (ReferenceSourcePrefixHistoryFiltration.incoming_measurable
      rate rewards C_star C_h control0 t)
  have hset := hquery (MeasurableSet.singleton true)
  have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
      issuedAt rate rewards C_star C_h t z} =
      {z | issuedIncomingCode rate t
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z) = true} := by
    ext z
    exact issuedAt_iff_incoming_code_query rate rewards C_star C_h t z
  rw [heq]
  exact hset

/-- The first issued collection command, with the source-horizon sentinel
when no command occurs. -/
def S
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (issuedDateIndices rate rewards C_star C_h z).Nonempty then
    ((issuedDateIndices rate rewards C_star C_h z).min' h).val + 1
  else p.T + 1

theorem mem_issuedDateIndices_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) :
    t ∈ issuedDateIndices rate rewards C_star C_h z ↔
      issuedAt rate rewards C_star C_h t z := by
  simp [issuedDateIndices]

theorem issuedAt_implies_S_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (ht : issuedAt rate rewards C_star C_h t z) :
    S rate rewards C_star C_h z ≤ t.val + 1 := by
  classical
  have hmem : t ∈ issuedDateIndices rate rewards C_star C_h z :=
    (mem_issuedDateIndices_iff rate rewards C_star C_h z t).2 ht
  have hne : (issuedDateIndices rate rewards C_star C_h z).Nonempty := ⟨t, hmem⟩
  rw [S, dite_eq_left hne]
  have hmin := Finset.min'_le (issuedDateIndices rate rewards C_star C_h z) t hmem
  exact Nat.add_le_add_right (Fin.le_iff_val_le_val.mp hmin) 1

theorem S_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    1 ≤ S rate rewards C_star C_h z ∧ S rate rewards C_star C_h z ≤ p.T + 1 := by
  classical
  by_cases h : (issuedDateIndices rate rewards C_star C_h z).Nonempty
  · rw [S, dite_eq_left h]
    let t := (issuedDateIndices rate rewards C_star C_h z).min' h
    have ht := t.isLt
    exact ⟨by omega, by omega⟩
  · rw [S, dite_eq_right h]
    exact ⟨by omega, le_rfl⟩

theorem S_eq_horizon_sentinel_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    S rate rewards C_star C_h z = p.T + 1 ↔
      ∀ t, ¬ issuedAt rate rewards C_star C_h t z := by
  classical
  constructor
  · intro hS t ht
    have hle := issuedAt_implies_S_le rate rewards C_star C_h z t ht
    have htT := t.isLt
    omega
  · intro hnone
    rw [S]
    split
    · next hne =>
        obtain ⟨t, ht⟩ := hne
        exact False.elim (hnone t
          ((mem_issuedDateIndices_iff rate rewards C_star C_h z t).1 ht))
    · rfl

theorem S_eq_horizon_sentinel_of_no_launch
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hno : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h p.T z) :
    S rate rewards C_star C_h z = p.T + 1 := by
  apply (S_eq_horizon_sentinel_iff rate rewards C_star C_h z).2
  intro t ht
  rcases ht with ⟨r, hr, reg, owned, base, hcoord, out, hstart, hcommand⟩
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z := by
    by_contra hnot
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hnot] at hr
    cases hr
  have ht := t.isLt
  rcases hlaunch with ⟨hc, hstart⟩
  exact hno ⟨hc, by omega⟩

theorem S_eq_horizon_sentinel_of_terminal_launch
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = p.T) :
    S rate rewards C_star C_h z = p.T + 1 := by
  apply (S_eq_horizon_sentinel_iff rate rewards C_star C_h z).2
  intro t ht
  rcases ht with ⟨r, hr, reg, owned, base, hcoord, out, hstart, hcommand⟩
  have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_terminal_start
    rate rewards C_star C_h t z hterminal
  rw [hnone] at hr
  cases hr


/-- Exact first-date characterization: the command occurs at `t` and no
earlier calendar date has issued one. -/
theorem S_eq_date_iff_first_issued
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) :
    S rate rewards C_star C_h z = t.val + 1 ↔
      issuedAt rate rewards C_star C_h t z ∧
        ∀ u : Fin p.T, u.val < t.val → ¬ issuedAt rate rewards C_star C_h u z := by
  classical
  constructor
  · intro hS
    have hne : (issuedDateIndices rate rewards C_star C_h z).Nonempty := by
      by_contra hne
      have hsent : S rate rewards C_star C_h z = p.T + 1 := by simp [S, hne]
      have ht := t.isLt
      omega
    let m := (issuedDateIndices rate rewards C_star C_h z).min' hne
    have hmS : m.val + 1 = t.val + 1 := by
      have hm : S rate rewards C_star C_h z = m.val + 1 := by simp [S, hne, m]
      omega
    have hmEq : m = t := Fin.ext (by omega)
    have hmIssued := (mem_issuedDateIndices_iff rate rewards C_star C_h z m).1
      (Finset.min'_mem (issuedDateIndices rate rewards C_star C_h z) hne)
    rw [hmEq] at hmIssued
    refine ⟨hmIssued, ?_⟩
    intro u hut hu
    have huMem := (mem_issuedDateIndices_iff rate rewards C_star C_h z u).2 hu
    have hmLe := Finset.min'_le (issuedDateIndices rate rewards C_star C_h z) u huMem
    have hmLe' : t ≤ u := hmEq ▸ hmLe
    exact (not_le_of_gt hut) (Fin.le_iff_val_le_val.mp hmLe')
  · rintro ⟨htIssued, hnoEarlier⟩
    have hne : (issuedDateIndices rate rewards C_star C_h z).Nonempty :=
      ⟨t, (mem_issuedDateIndices_iff rate rewards C_star C_h z t).2 htIssued⟩
    rw [S, dite_eq_left hne]
    have hmin := Finset.min'_mem (issuedDateIndices rate rewards C_star C_h z) hne
    have hminIssued := (mem_issuedDateIndices_iff rate rewards C_star C_h z _).1 hmin
    have hminLe := Finset.min'_le (issuedDateIndices rate rewards C_star C_h z) t
      ((mem_issuedDateIndices_iff rate rewards C_star C_h z t).2 htIssued)
    have hminEq : (issuedDateIndices rate rewards C_star C_h z).min' hne = t := by
      apply Fin.ext
      by_contra hneVal
      have hlt : ((issuedDateIndices rate rewards C_star C_h z).min' hne).val < t.val := by
        have := Fin.le_iff_val_le_val.mp hminLe
        omega
      exact hnoEarlier _ hlt hminIssued
    rw [hminEq]

/-- The first issued cutoff is a pre-round stopping time in the original
source-prefix filtration. -/
theorem S_is_pre_round_stopping_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (S rate rewards C_star C_h) := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  change ∀ v, MeasurableSet[F v] {z | S rate rewards C_star C_h z ≤ v}
  intro v
  by_cases hv0 : v = 0
  · subst v
    have heq : {z | S rate rewards C_star C_h z ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hpos := (S_bounds rate rewards C_star C_h z).1
      omega
    rw [heq]
    exact @MeasurableSet.empty (BootstrapPrivateRoundStreams.SourceInput p) (F 0)
  · by_cases hvT : p.T + 1 ≤ v
    · have heq : {z | S rate rewards C_star C_h z ≤ v} = Set.univ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact le_trans (S_bounds rate rewards C_star C_h z).2 hvT
      rw [heq]
      exact MeasurableSet.univ
    · have hvle : v ≤ p.T := by omega
      have hset : {z : BootstrapPrivateRoundStreams.SourceInput p |
          S rate rewards C_star C_h z ≤ v} =
          ⋃ t : Fin p.T,
            {z | t.val + 1 ≤ v ∧ issuedAt rate rewards C_star C_h t z} := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
        constructor
        · intro hSv
          have hne : (issuedDateIndices rate rewards C_star C_h z).Nonempty := by
            by_contra hne
            have hsent : S rate rewards C_star C_h z = p.T + 1 := by simp [S, hne]
            rw [hsent] at hSv
            omega
          let t := (issuedDateIndices rate rewards C_star C_h z).min' hne
          have hmem := Finset.min'_mem (issuedDateIndices rate rewards C_star C_h z) hne
          have hissued := (mem_issuedDateIndices_iff rate rewards C_star C_h z t).1 hmem
          have hS : S rate rewards C_star C_h z = t.val + 1 := by simp [S, hne, t]
          exact ⟨t, by rw [hS] at hSv; omega, hissued⟩
        · rintro ⟨t, htv, htIssued⟩
          exact (issuedAt_implies_S_le rate rewards C_star C_h z t htIssued).trans htv
      rw [hset]
      apply MeasurableSet.iUnion
      intro t
      by_cases htv : t.val + 1 ≤ v
      · have hmono : F (t.val + 1) ≤ F v := F.mono (by omega)
        have hi := issuedAt_measurable rate rewards C_star C_h control0 t
        simpa [htv] using
          hmono {z | issuedAt rate rewards C_star C_h t z} hi
      · simp [htv]



/-- Every nonempty actual record carries its real calendar coordinate.  The
identity is recovered from the actual corrected launch and the accepted run
record constructor. -/
theorem actualRecord_input_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    r.input.time = t := by
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z := by
    by_contra hnot
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hnot] at hr
    cases hr
  have hsome := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate z rewards C_star C_h).2 hlaunch.1
  cases hactive : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none => simp [hactive] at hsome
  | some active =>
      have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
        rate rewards C_star C_h t z active hactive hlaunch.2
      have heq := Option.some.inj (hrec.symm.trans hr)
      subst r
      apply Fin.ext
      simp [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
        ReferenceActivePhysicalHorizon.roundInputAt]
      have hstart := hlaunch.2
      omega

/-- Recover the command from an equality with the computed dispatcher,
retaining the raw cutoff dispatch and checked-initialization equations. -/
private theorem dispatchLive_cutoff_command
    (input : CoordinatorRoundDispatch.LiveInput p)
    (out : CoordinatorStartRoundCutoffDispatch.Output input.registers
      input.ownedRegisters input.followerBaseScore)
    (hs ledger hi he hd hc hp hn selection)
    (h : CoordinatorRoundDispatch.dispatchLive input =
      .cutoffChosen out hs ledger hi he hd hc hp hn selection) :
    out.startResult.ledgerCommand = some (.initializeAt input.registers.time) := by
  classical
  unfold CoordinatorRoundDispatch.dispatchLive at h
  dsimp only at h
  split at h
  · cases h
  · rename_i actual hactual
    have hstart := CoordinatorRoundDispatch.cutoffDispatch_startResult_eq
      input.registers input.ownedRegisters input.followerBaseScore actual hactual
    split at h
    · cases h
    · cases h
    · have hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame input.registers actual.startResult := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hframe] at h
      have hpayload : input.registers.priorClock.sigma = some input.registers.payload.sigma := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hpayload] at h
      have hgrid : input.registers.gridBoundary = input.registers.priorClock.g := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hgrid] at h
      have hscore : input.registers.scoreDomainValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hscore] at h
      have hqueue : input.ownedRegisters.queueDomainValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hqueue] at h
      have hprevious : input.ownedRegisters.previousServiceDomainValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hprevious] at h
      have hbase : ∀ i, input.followerBaseScore i ≤ p.T * D p := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hbase] at h
      have hlive : CoordinatorLocalArmChoice.assignmentIsLive input.registers.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
          input.registers.time := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hlive] at h
      have hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid input.registers.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
          input.registers.time input.registers.complementWeights := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hchoice] at h
      have hboundary : actual.startResult.clock.g ≤ p.T + 1 := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left hboundary] at h
      have henvelope : input.registers.complementEnvelopeValid := by
        by_contra hbad
        rw [dite_eq_right hbad] at h
        cases h
      rw [dite_eq_left henvelope] at h
      split at h
      · rename_i ha
        exact (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          _ _ _ _ _ _ hchoice ha).elim
      · cases h
    · rename_i candidate hcandidate
      have hcommand := (CoordinatorRoundDispatch.cutoffDispatch_ledger_eq_candidate
        input.registers input.ownedRegisters input.followerBaseScore actual candidate
        hactual hcandidate).1
      have hresults := Except.ok.inj (hstart.symm.trans hs)
      exact (congrArg CoordinatorPhaseClock.StartRoundResult.ledgerCommand hresults).symm.trans
        hcommand

private def liveCutoffChosen (x : CoordinatorRoundDispatch.LiveInput p) :
    CoordinatorRoundDispatch.LiveOutcome x → Bool
  | .cutoffChosen _ _ _ _ _ _ _ _ _ _ => true
  | _ => false

private theorem dispatchLive_issued_command
    (x : CoordinatorRoundDispatch.LiveInput p)
    (hchosen : liveCutoffChosen x (CoordinatorRoundDispatch.dispatchLive x) = true) :
    ∃ out, CoordinatorPhaseClock.startRound p x.eta.val x.registers.time
      x.registers.priorClock x.registers.clockPending = .ok out ∧
      out.ledgerCommand = some (.initializeAt x.registers.time) := by
  cases hactual : CoordinatorRoundDispatch.dispatchLive x with
  | clockFailure failure heq => simp [hactual, liveCutoffChosen] at hchosen
  | initializerFailure out hs checked heq => simp [hactual, liveCutoffChosen] at hchosen
  | localFailure out hs reason => simp [hactual, liveCutoffChosen] at hchosen
  | continuingChosen out hs continuation selected =>
      simp [hactual, liveCutoffChosen] at hchosen
  | cutoffChosen out hs ledger hi he hd hc hp hn selected =>
      exact ⟨out.startResult, hs,
        dispatchLive_cutoff_command x out hs ledger hi he hd hc hp hn selected hactual⟩

private theorem live_chosen_issued_command
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (reg : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters reg)
    (base : Fin (p.m - 1) → ℕ)
    (hcoord : x.state.coordinator = .live reg owned base)
    (hchosen : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ∃ out, CoordinatorPhaseClock.startRound p rate.eta.val x.time
      reg.priorClock reg.pendingAtChoice = .ok out ∧
      out.ledgerCommand = some (.initializeAt x.time) := by
  have htag : ReferenceCollectionPhaseHistory.cutoffChosen x =
      liveCutoffChosen (ReferenceActivePhysicalStep.liveInput x reg owned base)
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x reg owned base)) := by
    dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
      ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
    simp only [hcoord, CoordinatorRoundDispatch.dispatch]
    cases CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput x reg owned base) <;> rfl
  rw [htag] at hchosen
  exact dispatchLive_issued_command
    (ReferenceActivePhysicalStep.liveInput x reg owned base) hchosen

/-- Every actual chosen cutoff has an issued pre-choice command at its actual
calendar date. Failed commands are also retained by `issuedAt`. -/
private theorem issuedAt_of_actual_live_cutoffChosen
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r)
    (reg : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters reg)
    (base : Fin (p.m - 1) → ℕ)
    (hcoord : r.input.state.coordinator = .live reg owned base)
    (hchosen : ReferenceCollectionPhaseHistory.cutoffChosen r.input = true) :
    issuedAt rate rewards C_star C_h t z := by
  obtain ⟨out, hstart, hcommand⟩ := live_chosen_issued_command
    rate r.input reg owned base hcoord hchosen
  have htime := actualRecord_input_time rate rewards C_star C_h t z r hr
  rw [htime] at hstart hcommand
  exact ⟨r, hr, reg, owned, base, hcoord, out, hstart, hcommand⟩

/-- Nonempty awaited support has an actual issued cutoff no later than that
support date, without any favorable-path restriction. -/
private theorem S_le_of_Pawait_nonempty
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hP : (ReferenceFirstCollectionAwaitedTaskSupport.Pawait
      rate rewards C_star C_h t.val z).Nonempty) :
    S rate rewards C_star C_h z ≤ t.val + 1 := by
  have hraw : (ReferenceFirstCollectionPendingObservation.Praw
      rate rewards C_star C_h t.val z).Nonempty := by
    obtain ⟨i, hi⟩ := hP
    exact ⟨i, ((ReferenceFirstCollectionAwaitedTaskSupport.mem_Pawait_iff
      rate rewards C_star C_h t.val z i).1 hi).2⟩
  obtain ⟨⟨s0, u⟩, hpair⟩ :=
    (ReferenceFirstCollectionDetectedQueueMask.actual_pending_boundary_window
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      t z hraw).exists
  rcases hpair with ⟨hsu, hut, hC, _⟩
  dsimp only at hsu hut hC
  have huT : u < p.T := lt_of_le_of_lt hut t.isLt
  let date : Fin p.T := ⟨u, huT⟩
  have hback := (ReferenceFirstCollectionQueuePrefixChronology.active_boundary_backward
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (s := s0) (u := u) (t0 := date) (t1 := t) z hsu le_rfl hut hC).1
  rcases hback with ⟨_, r, hr, hb⟩
  have hissued : issuedAt rate rewards C_star C_h date z := by
    cases hcoord : r.input.state.coordinator with
    | first => simp only [hcoord] at hb
    | dagger => simp only [hcoord] at hb
    | collection payload ledger proposal =>
        simp only [hcoord] at hb
        have hlt : u < u := hb.1
        omega
    | live reg owned base =>
        simp only [hcoord] at hb
        exact issuedAt_of_actual_live_cutoffChosen rate rewards C_star C_h
          date z r hr reg owned base hcoord hb.2.2
  exact (issuedAt_implies_S_le rate rewards C_star C_h z date hissued).trans
    (Nat.add_le_add_right hut 1)

/-- The first issued cutoff precedes the first nonempty awaited date on
EVERY sample of the original source space. -/
theorem S_le_sigma
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    S rate rewards C_star C_h z ≤
      ReferenceFirstCollectionAwaitedPhaseSupport.sigma
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z := by
  classical
  unfold ReferenceFirstCollectionAwaitedPhaseSupport.sigma
  split
  · rename_i hne
    have hm := Finset.min'_mem _ hne
    have hsupport := (ReferenceFirstCollectionAwaitedPhaseSupport.mem_supportIndices_iff
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z _).1 hm
    exact S_le_of_Pawait_nonempty rate rewards C_star C_h
      ⟨_, hsupport.1⟩ z hsupport.2
  · exact (S_bounds rate rewards C_star C_h z).2

/-- The existing stopped history field at the first actual issued cutoff. -/
@[instance_reducible] def GammaS
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
  PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
    (S rate rewards C_star C_h)
    (S_is_pre_round_stopping_time rate rewards C_star C_h control0)

/-- The unchanged awaited-support stopped field used by the waiting bound. -/
@[instance_reducible] def GammaSigma
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
  PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
    (ReferenceFirstCollectionAwaitedPhaseSupport.sigma
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h))
    (ReferenceFirstCollectionAwaitedPhaseSupport.sigma_is_pre_round_stopping_time
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0)

/-- Earlier actual cutoff histories are included in the original awaited
support history, using Mathlib's stopped σ-algebras. -/
theorem GammaS_le_GammaSigma
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    GammaS rate rewards C_star C_h control0 ≤
      GammaSigma rate rewards C_star C_h control0 := by
  unfold GammaS GammaSigma PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
  apply MeasureTheory.IsStoppingTime.measurableSpace_mono
  intro z
  change (S rate rewards C_star C_h z : WithTop ℕ) ≤
    (ReferenceFirstCollectionAwaitedPhaseSupport.sigma
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z : WithTop ℕ)
  exact WithTop.coe_le_coe.mpr (S_le_sigma rate rewards C_star C_h z)

/-- Both stopped fields retain the original source-input ambient space. -/
theorem GammaSigma_le_ambient
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    GammaSigma rate rewards C_star C_h control0 ≤
      inferInstanceAs (MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p)) := by
  exact PhaseStartConditionalWaiting.phaseStartSigmaAlgebra_le _ _ _

theorem GammaS_le_ambient
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    GammaS rate rewards C_star C_h control0 ≤
      inferInstanceAs (MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p)) := by
  exact (GammaS_le_GammaSigma rate rewards C_star C_h control0).trans
    (GammaSigma_le_ambient rate rewards C_star C_h control0)

/-- The downward tower for the SAME actual awaited waiting charge and the
original source-input law at the earlier issued-cutoff history. -/
theorem actual_awaited_waiting_charge_downward_tower
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        ReferenceFirstCollectionAwaitedWaitingCost.actualFirstCollectionAwaitedWaitingCharge
          rate rewards C_star C_h | GammaSigma rate rewards C_star C_h control0] |
        GammaS rate rewards C_star C_h control0] =ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        ReferenceFirstCollectionAwaitedWaitingCost.actualFirstCollectionAwaitedWaitingCharge
          rate rewards C_star C_h | GammaS rate rewards C_star C_h control0] := by
  exact MeasureTheory.condExp_condExp_of_le
    (GammaS_le_GammaSigma rate rewards C_star C_h control0)
    (GammaSigma_le_ambient rate rewards C_star C_h control0)

/-- Integrability under the unchanged original source-input law. -/
theorem actual_awaited_waiting_charge_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable
      (ReferenceFirstCollectionAwaitedWaitingCost.actualFirstCollectionAwaitedWaitingCharge
        rate rewards C_star C_h)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  exact ReferenceFirstCollectionAwaitedWaitingCost.actual_first_collection_awaited_waiting_charge_integrable
      rate rewards C_star C_h control0

/-- Every event measurable at the earlier issued cutoff has the SAME
unnormalized awaited-charge estimate, including zero-mass events. -/
theorem actual_awaited_waiting_charge_setIntegral_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hB : MeasurableSet[GammaS rate rewards C_star C_h control0] B) :
    (∫ z in B,
      ReferenceFirstCollectionAwaitedWaitingCost.actualFirstCollectionAwaitedWaitingCharge
        rate rewards C_star C_h z ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
  exact ReferenceFirstCollectionAwaitedWaitingCost.actual_first_collection_awaited_waiting_charge_setIntegral_bound
      rate rewards C_star C_h control0 B
      (GammaS_le_GammaSigma rate rewards C_star C_h control0 B hB)

/-- The SAME awaited charge is conditionally bounded by `Bcol` at the actual
first issued-cutoff history, on the original full source law. -/
theorem actual_awaited_waiting_charge_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      ReferenceFirstCollectionAwaitedWaitingCost.actualFirstCollectionAwaitedWaitingCharge
        rate rewards C_star C_h | GammaS rate rewards C_star C_h control0] ≤ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun _ => ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) := by
  apply (PhaseStartConditionalWaiting.setIntegral_iff_condExp_le
    (BootstrapPrivateRoundStreams.sourceInputLaw p)
    (GammaS rate rewards C_star C_h control0)
    (GammaS_le_ambient rate rewards C_star C_h control0)
    (ReferenceFirstCollectionAwaitedWaitingCost.actualFirstCollectionAwaitedWaitingCharge
      rate rewards C_star C_h)
    (ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p))
    (actual_awaited_waiting_charge_integrable rate rewards C_star C_h control0)).1
  exact actual_awaited_waiting_charge_setIntegral_bound rate rewards C_star C_h control0

end Bandits.Support.ReferenceFirstCollectionAwaitedCutoffHistory

end
