/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostInvocationKilledJointLaw

import Mathlib.Tactic

/-!
# Retained post-invocation endpoint recurrence

Pointwise address and recurrence identities on the original inserted physical
source and original auxiliary array. The evaluator view exchanges the two
labels at the produced invocation only in the renewed branch. It does not
change the observed array, produced cell, source, or generated history.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:176-215`, and `08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Bandits.Support
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInstallationCellFactors
open ReferenceFirstCollectionLogicalNumericalAlignment
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationGeneratedAlignment
open ReferenceActualCollectionHiddenRefreshPath
open ReferenceCompletePhysicalHistory
open ReferenceFirstLaunchNumericalCell (queueParameters)

namespace Bandits.Support.ReferencePostInvocationRetainedEndpointRecurrence

variable {p : ConstructorDimensions.Parameters}

abbrev Coordinate := ReferenceFirstCollectionAuxiliarySeeds.Coordinate
abbrev Auxiliary := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray

/-- Address view for the canonical evaluator. Renewal has already consumed
label one for installation, so its residual at the same date reads label zero. -/
def evaluatorAddress (b : Bool) (t : Fin p.T) : Coordinate p ≃ Coordinate p :=
  if b then Equiv.swap (t, 0) (t, 1) else Equiv.refl _

/-- A view of the same original array; no invariance of its branch law is asserted. -/
def evaluatorArray (b : Bool) (t : Fin p.T) (a : Auxiliary p) : Auxiliary p :=
  fun j => a (evaluatorAddress b t j)

theorem evaluatorAddress_date (b : Bool) (t : Fin p.T) (j : Coordinate p) :
    (evaluatorAddress b t j).1 = j.1 := by
  cases b
  · rfl
  · change (Equiv.swap (t, 0) (t, 1) j).1 = j.1
    rw [Equiv.swap_apply_def]
    split_ifs with h0 h1
    · exact (congrArg Prod.fst h0).symm
    · exact (congrArg Prod.fst h1).symm
    · rfl

theorem evaluatorAddress_other_date (b : Bool) (t : Fin p.T) (j : Coordinate p)
    (h : j.1 ≠ t) : evaluatorAddress b t j = j := by
  cases b
  · rfl
  · exact Equiv.swap_apply_of_ne_of_ne
      (fun he => h (congrArg Prod.fst he)) (fun he => h (congrArg Prod.fst he))

theorem evaluatorArray_produced_residual (b : Bool) (t : Fin p.T) (a : Auxiliary p) :
    evaluatorArray b t a (t, 1) = a (t, if b then 0 else 1) := by
  cases b
  · rfl
  · exact congrArg a (Equiv.swap_apply_right (t, 0) (t, 1))

theorem evaluatorArray_other_date (b : Bool) (t : Fin p.T) (a : Auxiliary p)
    (j : Coordinate p) (h : j.1 ≠ t) : evaluatorArray b t a j = a j := by
  exact congrArg a (evaluatorAddress_other_date b t j h)

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (e n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p)
  (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e n)

/-- The evaluator's consumed addresses in the original branch array. -/
def consumedAddress (b : Bool) (t : Fin p.T) (k : ℕ) (hk : k ≤ n - e) :
    Unit ⊕ (Fin k ⊕ Fin k) → Coordinate p :=
  fun i => evaluatorAddress b t
    (actualCoordinateIndex rate rewards C_star C_h e n z hz k hk i)

theorem consumedAddress_injective (b : Bool) (t : Fin p.T) (k : ℕ) (hk : k ≤ n - e) :
    Function.Injective (consumedAddress rate rewards C_star C_h e n z hz b t k hk) :=
  (evaluatorAddress b t).injective.comp
    (actualCoordinateIndex_injective rate rewards C_star C_h e n z hz k hk)

/-- Once the actual trigger is at or after the produced date, every consumed
address belongs to the branch's genuinely unused block, including equality. -/
theorem consumedAddress_unused (b : Bool) (t : Fin p.T)
    (htrigger : t.val ≤ physicalStart rate z rewards C_star C_h + e - 1)
    (k : ℕ) (hk : k ≤ n - e) (i : Unit ⊕ (Fin k ⊕ Fin k)) :
    let j := consumedAddress rate rewards C_star C_h e n z hz b t k hk i
    t.val < j.1.val ∨ (j.1 = t ∧ j.2 = if b then 0 else 1) := by
  dsimp only
  have hepos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e n z hz
  have hdate := evaluatorAddress_date b t
    (actualCoordinateIndex rate rewards C_star C_h e n z hz k hk i)
  rcases i with ⟨⟩ | (i | i)
  · have hc := actualCoordinateIndex_trigger rate rewards C_star C_h e n z hz k hk
    by_cases he : t.val = physicalStart rate z rewards C_star C_h + e - 1
    · have hj : actualCoordinateIndex rate rewards C_star C_h e n z hz k hk (.inl ()) = (t, 1) := by
        apply Prod.ext
        · exact Fin.ext (hc.1.trans he.symm)
        · exact hc.2
      right
      cases b
      · exact ⟨congrArg Prod.fst hj, congrArg Prod.snd hj⟩
      · change (Equiv.swap (t, 0) (t, 1)
          (actualCoordinateIndex rate rewards C_star C_h e n z hz k hk (.inl ()))).1 = t ∧
          (Equiv.swap (t, 0) (t, 1)
            (actualCoordinateIndex rate rewards C_star C_h e n z hz k hk (.inl ()))).2 = 0
        rw [hj, Equiv.swap_apply_right]
        exact ⟨rfl, rfl⟩
    · left
      change t.val < (evaluatorAddress b t _).1.val
      rw [hdate, hc.1]
      omega
  · left
    change t.val < (evaluatorAddress b t _).1.val
    rw [hdate, (actualCoordinateIndex_step rate rewards C_star C_h e n z hz k hk i).1]
    omega
  · left
    change t.val < (evaluatorAddress b t _).1.val
    rw [hdate, (actualCoordinateIndex_step rate rewards C_star C_h e n z hz k hk i).2.2.1]
    omega

/-- Equality on the actual consumed original addresses suffices for the whole
canonical path, with no equality assumption on the rest of either array. -/
theorem sampledArrayPath_evaluator_ext (b : Bool) (t : Fin p.T)
    (k : ℕ) (hk : k ≤ n - e) (a a' : Auxiliary p)
    (h : ∀ i, a (consumedAddress rate rewards C_star C_h e n z hz b t k hk i) =
      a' (consumedAddress rate rewards C_star C_h e n z hz b t k hk i)) :
    sampledArrayPath rate rewards C_star C_h e n z hz k hk (evaluatorArray b t a) =
      sampledArrayPath rate rewards C_star C_h e n z hz k hk (evaluatorArray b t a') := by
  exact sampledArrayPath_eq_of_used_entries rate rewards C_star C_h e n z hz k hk
    (evaluatorArray b t a) (evaluatorArray b t a') h

/-- Literal injective allocation into the unused original branch block. The
date inequality is supplied by `retained_endpoint` on an actual next call. -/
def consumedEmbedding (b : Bool) (t : Fin p.T)
    (htrigger : t.val ≤ physicalStart rate z rewards C_star C_h + e - 1)
    (k : ℕ) (hk : k ≤ n - e) :
    (Unit ⊕ (Fin k ⊕ Fin k)) ↪
      {j : Coordinate p // t.val < j.1.val ∨ (j.1 = t ∧ j.2 = if b then 0 else 1)} where
  toFun i := ⟨consumedAddress rate rewards C_star C_h e n z hz b t k hk i,
    consumedAddress_unused rate rewards C_star C_h e n z hz b t htrigger k hk i⟩
  inj' _ _ h := consumedAddress_injective rate rewards C_star C_h e n z hz b t k hk
    (congrArg Subtype.val h)

local notation "Q" => queueParameters rate
local notation "start " x:max => physicalStart rate x rewards C_star C_h
local notation "records " x:max => completeSuffixRecords rate x rewards C_star C_h
local notation "recordAt" => ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
local notation "liveDomain" => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h
local notation "colDomain" => collectionDateDomain rate rewards C_star C_h
local notation "FirstSource" => FirstInvocationSource rate rewards C_star C_h
local notation "firstCell" => firstSourceCell rate rewards C_star C_h
local notation "W" => collectionWord rate rewards C_star C_h e n z hz
local notation "P" => oldPayload rate rewards C_star C_h e n z hz

private theorem numericalCoordinates_injective : Function.Injective
    (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates (p := p)) := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  cases h
  rfl

private theorem clear_before (k : ℕ) (hk : k ≤ n) :
    (collectionState rate rewards C_star C_h e n z hz k).overflow = false := by
  have hclear := collectionWord_retained rate rewards C_star C_h e n z hz
  have hbound := collectionWord_bound rate rewards C_star C_h e n z hz
  cases ho : (collectionState rate rewards C_star C_h e n z hz k).overflow with
  | false => rfl
  | true =>
      have hf := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q W k (hk.trans hbound)).mp ho
      have hn := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q W n hbound).mpr (hf.trans hk)
      rw [show (RecordedQueueRun.run Q ((W).take n)).overflow = false from hclear] at hn
      cases hn

private theorem cutoff_not_later
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (h : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ReferenceCollectionPhaseHistory.laterChosen x = false := by
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at h
  unfold ReferenceCollectionPhaseHistory.laterChosen
  cases hc : (ReferenceActivePhysicalStep.prepare x).coordinator <;> simp only [hc] at h ⊢
  next r q base outcome => cases outcome <;> simp_all only

private theorem continuing_not_cutoff
    (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (h : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r = true) :
    ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
  have hp : (ReferenceActivePhysicalStep.prepare r.input).coordinator =
      r.output.preparation.coordinator := by rw [r.output_eq]; rfl
  unfold ReferenceCollectionPhaseHistory.cutoffChosen
  rw [hp]
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at h
  cases hc : r.output.preparation.coordinator <;> simp only [hc] at h ⊢
  next r q base outcome => cases outcome <;> simp_all only

private theorem collection_not_live (v : Fin p.T) (hc : z ∈ colDomain v) :
    z ∉ liveDomain v := by
  intro hl
  have hr := (continuingSourceCell_spec rate rewards C_star C_h v ⟨z, hl⟩).1
  have hcR := (collectionRecord_spec rate rewards C_star C_h v ⟨z, hc⟩).1
  have heq := Option.some.inj (hr.symm.trans hcR)
  have hread := (continuingSourceCell_spec rate rewards C_star C_h v ⟨z, hl⟩).2.1
  have hcol := collectionInput_readout rate rewards C_star C_h v ⟨z, hc⟩
  rw [heq] at hread
  exact ReferenceCompleteNumericalBranchObservation.readouts_disjoint rate 0 _
    ⟨by rw [hread]; rfl, by rw [hcol]; rfl⟩

/-- The original produced source, with its accepted first-invocation subtype. -/
def producedSource (b : Bool) (u t : Fin p.T)
    (w : BranchLift rate rewards C_star C_h b u t) : FirstSource t := match b with
  | false => nonrenewedFirstSource rate rewards C_star C_h t u w.1.1 w.2
  | true => renewedFirstSource rate rewards C_star C_h t u
      (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t w).2

theorem producedSource_val (control0 : ContinuousLearningRows.TimeControl p)
    (b : Bool) (u t : Fin p.T) (w : BranchLift rate rewards C_star C_h b u t) :
    (producedSource rate rewards C_star C_h b u t w).val =
      insertedPhysicalSource rate (branchTransition rate rewards C_star C_h control0 b u t w) := by
  cases b <;> rfl

theorem produced_cell (control0 : ContinuousLearningRows.TimeControl p)
    (b : Bool) (u t : Fin p.T) (w : BranchLift rate rewards C_star C_h b u t) :
    (branchTransition rate rewards C_star C_h control0 b u t w).2.2.2 =
      actualFirstCell rate rewards C_star C_h control0 t
        (producedSource rate rewards C_star C_h b u t w) (w.1.2 (t, if b then 0 else 1)) := by
  cases b <;> rfl

theorem producedSource_sigma (b : Bool) (u t : Fin p.T)
    (w : BranchLift rate rewards C_star C_h b u t) :
    (firstCell t (producedSource rate rewards C_star C_h b u t w)).selected.view.payload.sigma = t := by
  obtain ⟨i, rb, _qb, _base, hr, _heq, _chosen, _next, hb, hp⟩ :=
    firstInvocation_installation rate rewards C_star C_h t
      (producedSource rate rewards C_star C_h b u t w)
  apply Fin.ext
  rw [← hp]
  exact (ReferenceAssignmentPayloadChronology.installationBirth_time_eq _ _ hb).trans
    (congrArg Fin.val (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t _ _ hr).2.2.1)

include hz in
/-- A canonical retained window at a later PRE boundary starts strictly after
the actual produced installation. The trigger may be exactly the produced date. -/
theorem produced_before_cutoff (t q : Fin p.T) (htq : t.val < q.val)
    (s : FirstSource t) (hs : s.val = z) (hdate : start z + n = q.val) :
    t.val < start z + e := by
  subst z
  obtain ⟨i, _rb, _qb, _base, hr, _heq, hlater, _⟩ :=
    firstInvocation_installation rate rewards C_star C_h t s
  obtain ⟨j, hj, hrecord, hstart⟩ := actualRecord_index rate rewards C_star C_h t s.val _ hr
  have hsame : i.val = j.val := by
    have hi := congrArg (fun r => r.input.time.val) hrecord
    have ht := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
      rate s.val rewards C_star C_h j.val _ (List.getElem?_eq_getElem j.isLt)
    have hti := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t s.val _ hr).2.2.1
    have htimeI := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
      rate s.val rewards C_star C_h i.val _ (List.getElem?_eq_getElem i.isLt)
    omega
  have hlaterJ : ReferenceCollectionPhaseHistory.laterChosen (records s.val)[j.val].input = true := by
    simpa only [hsame] using hlater
  obtain ⟨he, r, owned, base, hlive, hcut, _⟩ :=
    collectionPrefixCell_live rate rewards C_star C_h e n s.val hz
  have hno : ∀ k : Fin (records s.val).length, e < k.val → k.val < n →
      ReferenceCollectionPhaseHistory.laterChosen (records s.val)[k.val].input = false := by
    obtain ⟨_, _, _, hc⟩ := hz
    rw [hlive] at hc
    exact hc.2.2.1
  have hje : e < j.val ∨ e = j.val ∨ j.val < e := by omega
  rcases hje with hlt | heq | hlt
  · have hn := hno j hlt (by omega)
    rw [hlaterJ] at hn
    cases hn
  · have hn := cutoff_not_later rate (records s.val)[e].input hcut
    have ht : ReferenceCollectionPhaseHistory.laterChosen (records s.val)[e].input = true := by
      simpa only [← heq] using hlaterJ
    rw [ht] at hn
    cases hn
  · omega

/-- The canonical old payload is the one installed by the produced invocation. -/
theorem oldPayload_eq_produced (t q : Fin p.T) (htq : t.val < q.val)
    (s : FirstSource t) (hs : s.val = z) (hdate : start z + n = q.val)
    (hcall : NoCallBetween rate rewards C_star C_h t q.castSucc z) :
    P = (firstCell t s).selected.view.payload := by
  subst z
  have hafter := produced_before_cutoff rate rewards C_star C_h e n s.val hz t q htq s rfl hdate
  obtain ⟨he, r, owned, base, hlive, _hcut, _hboundary, hp⟩ :=
    collectionPrefixCell_live rate rewards C_star C_h e n s.val hz
  let v := cutoffDate rate rewards C_star C_h e n s.val hz
  have hv : recordAt v s.val = some (records s.val)[e] := by
    change (if start s.val ≤ v.val then (records s.val)[v.val - start s.val]? else none) = _
    have hstart : start s.val ≤ v.val := by dsimp only [v, cutoffDate]; omega
    rw [ite_eq_left hstart]
    have hi : v.val - start s.val = e := by dsimp only [v, cutoffDate]; omega
    rw [hi, List.getElem?_eq_getElem he]
  have hret := (firstInvocation_retained_interval rate rewards C_star C_h t q.castSucc s
    hcall).1 v hafter (by change start s.val + e ≤ q.val; have := hz.1; omega) _ hv
  rw [hlive, ReferenceAssignmentPayloadPersistence.storedPayload_live] at hret
  exact (oldPayload_eq rate rewards C_star C_h e n s.val hz r.payload hp).trans
    (Option.some.inj hret)

private theorem cutoff_record :
    recordAt (cutoffDate rate rewards C_star C_h e n z hz) z =
      some ((records z)[e]'(collectionPrefixCell_live rate rewards C_star C_h e n z hz).choose) := by
  have he := (collectionPrefixCell_live rate rewards C_star C_h e n z hz).choose
  change (if start z ≤ start z + e then (records z)[start z + e - start z]? else none) = _
  rw [ite_eq_left (by omega), Nat.add_sub_cancel_left, List.getElem?_eq_getElem he]

include hz in
private theorem window_collection_domain (t q : Fin p.T) (htq : t.val < q.val)
    (s : FirstSource t) (hs : s.val = z) (hdate : start z + n = q.val)
    (hcall : NoCallBetween rate rewards C_star C_h t q.castSucc z)
    (k : ℕ) (hk : e + k < n) :
    z ∈ colDomain ⟨start z + e + k, by omega⟩ := by
  have hafter := produced_before_cutoff rate rewards C_star C_h e n z hz t q htq s hs hdate
  have hepos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e n z hz
  induction k with
  | zero =>
      let v := cutoffDate rate rewards C_star C_h e n z hz
      have hnocall := hcall v hafter (by change start z + e < q.val; omega)
      rcases noncall_phase_coverage rate rewards C_star C_h v z (by change start z < start z + e; omega)
        hnocall with hl | hc
      · obtain ⟨r, owned, base, started, _hin, hcont, _⟩ :=
          continuingRecord_frame rate rewards C_star C_h v ⟨z, hl⟩
        have hr := (continuingSourceCell_spec rate rewards C_star C_h v ⟨z, hl⟩).1
        have heq := Option.some.inj (hr.symm.trans (cutoff_record rate rewards C_star C_h e n z hz))
        have hn := continuing_not_cutoff rate _ hcont
        rw [heq] at hn
        have hc := (collectionPrefixCell_live rate rewards C_star C_h e n z hz).choose_spec.choose_spec.choose_spec.choose_spec.2.1
        rw [hc] at hn
        cases hn
      · exact hc
  | succ k ih =>
      let v : Fin p.T := ⟨start z + e + k, by omega⟩
      let v' : Fin p.T := ⟨start z + e + (k + 1), by omega⟩
      have hc : z ∈ colDomain v := ih (by omega)
      have hv := (collectionRecord_spec rate rewards C_star C_h v ⟨z, hc⟩).1
      obtain ⟨ledger, saved, hout⟩ := collectionRecord_output rate rewards C_star C_h v ⟨z, hc⟩
      have hnocall := hcall v' (by dsimp only [v']; omega) (by change start z + e + (k + 1) < q.val; omega)
      rcases noncall_phase_coverage rate rewards C_star C_h v' z (by dsimp only [v']; omega)
        hnocall with hl | hc'
      · obtain ⟨r, owned, base, started, hin, _⟩ :=
          continuingRecord_frame rate rewards C_star C_h v' ⟨z, hl⟩
        have hv' := (continuingSourceCell_spec rate rewards C_star C_h v' ⟨z, hl⟩).1
        have hadj := congrArg ReferenceActivePhysicalStep.State.coordinator
          (actualRecord_adjacent rate rewards C_star C_h v v' (by dsimp only [v, v']; omega)
            z _ _ hv hv')
        rw [hin, hout] at hadj
        cases hadj
      · exact hc'

/-- On a disabled collection date the generated seed and list are both
retained, even though the physical numerical calendar advances. -/
theorem appendNoncallDate_collection_disabled (v : Fin p.T) (hc : z ∈ colDomain v)
    (a : Auxiliary p) (state : SlowSet p × List (LogicalCell p rate))
    (he : (collectionInput rate rewards C_star C_h v ⟨z, hc⟩).enabled = false) :
    appendNoncallDate rate rewards C_star C_h v z a state = state := by
  rw [appendNoncallDate, noncallDateCell,
    dite_eq_right (collection_not_live rate rewards C_star C_h z v hc), dite_eq_left hc,
    laterCollectionCell?, he, ite_eq_right (by decide : ¬ false = true)]

/-- PRE-clear collection uses the canonical refresh evaluator on exactly the
same input, old anchor, incoming set, and original dated pair. -/
theorem appendNoncallDate_collection_refresh (v : Fin p.T) (hc : z ∈ colDomain v)
    (a : Auxiliary p) (state : SlowSet p × List (LogicalCell p rate))
    (hclear : (collectionBefore rate rewards C_star C_h v ⟨z, hc⟩).overflow = false) :
    (appendNoncallDate rate rewards C_star C_h v z a state).1 =
      DeferredRefreshUniformKernels.sampleRecordedRefresh p Q
        (collectionBefore rate rewards C_star C_h v ⟨z, hc⟩)
        (collectionInput rate rewards C_star C_h v ⟨z, hc⟩)
        (collectionArguments rate rewards C_star C_h v ⟨z, hc⟩).1.anchor
        (collectionArguments rate rewards C_star C_h v ⟨z, hc⟩).1.anchor_pos
        state.1 (a (v, 0), a (v, 1)) := by
  cases he : (collectionInput rate rewards C_star C_h v ⟨z, hc⟩).enabled with
  | false =>
      rw [appendNoncallDate_collection_disabled rate rewards C_star C_h z v hc a state he]
      exact (DeferredRefreshUniformKernels.sampleRecordedRefresh_eq_current_of_inactive
        p Q _ _ _ _ _ (Or.inl he) _).symm
  | true =>
      rw [appendNoncallDate, noncallDateCell,
        dite_eq_right (collection_not_live rate rewards C_star C_h z v hc), dite_eq_left hc,
        laterCollectionCell?, he, ite_eq_left (rfl : true = true)]
      simp only [laterCollectionCell, hclear, he, Bool.not_false, Bool.true_and,
        Bool.false_eq_true, ite_false,
        DeferredRefreshUniformKernels.sampleRecordedRefresh,
        RecordedSlowRefresh.proposalProbability_active p Q _ _ hclear he,
        RecordedSlowRefresh.hazard, FollowerCutoffScan.thresholdProposalBit,
        decide_eq_true_eq]
      rfl

private theorem native_trigger_next
    (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (S : RecordedQueueRun.RunState p.K) (a : Auxiliary p)
    (hclear : S.overflow = false)
    (hbit : FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time = true) :
    (appendLogicalCell r c S a).nextSlowSet =
      DeferredRefreshUniformKernels.sampleResidual p Q S c.input
        c.selected.view.payload.anchor c.selected.view.payload.anchor_pos (a (r.input.time, 1)) := by
  simp only [appendLogicalCell, hclear, hbit, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ite_false, ite_true]
  rfl

private theorem trigger_initialization
    (control0 : ContinuousLearningRows.TimeControl p) (b : Bool) (u t q : Fin p.T)
    (htq : t.val < q.val) (s : FirstSource t) (hs : s.val = z)
    (hc : s.val ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (hdate : start z + n = q.val)
    (hcall : NoCallBetween rate rewards C_star C_h t q.castSucc z)
    (a : Auxiliary p) (H : List (LogicalCell p rate)) :
    (noncallCalendar rate rewards C_star C_h t z a
      ((actualFirstCell rate rewards C_star C_h control0 t s (a (t, if b then 0 else 1))).nextSlowSet, H)
      (start z + e)).map Prod.fst =
      some (triggerSampler rate rewards C_star C_h e n z hz
        (evaluatorArray b t a
          (actualCoordinateIndex rate rewards C_star C_h e n z hz (n - e) le_rfl (.inl ())))) := by
  have hepos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e n z hz
  have heb := hz.1
  have hafter := produced_before_cutoff rate rewards C_star C_h e n z hz t q htq s hs hdate
  have hP := oldPayload_eq_produced rate rewards C_star C_h e n z hz t q htq s hs hdate hcall
  let v : Fin p.T := ⟨start z + e - 1, by have := q.isLt; omega⟩
  let d := cutoffDate rate rewards C_star C_h e n z hz
  have hvd : v.val + 1 = d.val := by dsimp only [v, d, cutoffDate]; omega
  have htv : t.val ≤ v.val := by dsimp only [v]; omega
  have hstart : start z < t.val := by
    have hd := firstCall_dates rate rewards C_star C_h u t s.val hc
    simpa only [hs] using hd.1.trans_lt hd.2.1
  have hvq : v.val < q.val := by dsimp only [v]; omega
  have hi : v.val - start z = e - 1 := by dsimp only [v]; omega
  have haddr : actualCoordinateIndex rate rewards C_star C_h e n z hz (n - e) le_rfl (.inl ()) =
      (v, 1) := by
    apply Prod.ext
    · exact Fin.ext (actualCoordinateIndex_trigger rate rewards C_star C_h e n z hz _ _).1
    · exact (actualCoordinateIndex_trigger rate rewards C_star C_h e n z hz _ _).2
  rw [haddr]
  obtain ⟨stamp, hstamp, hproposal⟩ := collectionPrefixCell_trigger_proposal rate rewards C_star C_h e n z hz
  have hstampEq : stamp = v := Fin.ext (by change stamp.val + 1 = start z + e at hstamp; dsimp only [v]; omega)
  rw [hstampEq] at hproposal
  have hbit (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
      (hr : recordAt v z = some r) :
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time = true := by
    have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h v z r hr
    change FollowerCutoffScan.completeRowProposalBit p rate.eta.val (r.input.rows r.input.selected) r.input.time = true
    rw [hf.1, hf.2.1, hf.2.2.1]
    exact hproposal
  let initial := ((actualFirstCell rate rewards C_star C_h control0 t s
    (a (t, if b then 0 else 1))).nextSlowSet, H)
  have hfree : NoCallBetween rate rewards C_star C_h t d.castSucc z := by
    intro r htr hrd
    exact hcall r htr (by change r.val < q.val; change r.val < start z + e at hrd; omega)
  have hsome := (noncallCalendar_isSome rate rewards C_star C_h t d.castSucc z a initial).mpr hfree
  obtain ⟨state, hstate⟩ := Option.isSome_iff_exists.mp hsome
  change noncallCalendar rate rewards C_star C_h t z a initial (start z + e) = some state at hstate
  rw [hstate, Option.map_some]
  congr 1
  by_cases heq : v = t
  · have hinit := noncallCalendar_initial rate rewards C_star C_h t z a initial (start z + e)
      (by have hv := congrArg Fin.val heq; dsimp only [v] at hv; omega)
    have hstateEq := Option.some.inj (hstate.symm.trans hinit)
    rw [hstateEq]
    change (actualFirstCell rate rewards C_star C_h control0 t s (a (t, if b then 0 else 1))).nextSlowSet = _
    have hidx : t.val - start z = e - 1 := by rw [← heq]; exact hi
    have hn := actualFirstCell_originalWord rate rewards C_star C_h control0 u t s hc (a (t, if b then 0 else 1))
    have hbefore : firstBefore rate rewards C_star C_h control0 t s =
        collectionState rate rewards C_star C_h e n z hz (e - 1) := by
      simpa only [actualFirstCell, appendLogicalCell, collectionState, collectionWord, hs, hidx] using hn.2.1
    obtain ⟨hbound, hnum, _⟩ := hn.2.2.2
    have hinput : (firstCell t s).input = triggerInput rate rewards C_star C_h e n z hz := by
      apply numericalCoordinates_injective
      simpa only [actualFirstCell, appendLogicalCell, triggerInput, collectionWord, hs, hidx,
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates] using hnum
    have hclear : (firstBefore rate rewards C_star C_h control0 t s).overflow = false := by
      rw [hbefore]
      exact clear_before rate rewards C_star C_h e n z hz (e - 1) (by omega)
    have hr : recordAt v z = some (firstRecord rate rewards C_star C_h t s) := by
      simpa only [heq, hs] using (firstSourceCell_spec rate rewards C_star C_h t s).1
    rw [actualFirstCell, native_trigger_next rate _ _ _ _ hclear (hbit _ hr)]
    simp only [Function.update_self]
    rw [hbefore, hinput]
    rw [heq, evaluatorArray_produced_residual]
    simp only [triggerSampler, hP]
  · have hlt : t.val < v.val := lt_of_le_of_ne htv (fun h => heq (Fin.ext h.symm))
    have hncall := hcall v hlt hvq
    have hlive : z ∈ liveDomain v := by
      rcases noncall_phase_coverage rate rewards C_star C_h v z (by omega) hncall with hl | hcol
      · exact hl
      · have hvR := (collectionRecord_spec rate rewards C_star C_h v ⟨z, hcol⟩).1
        obtain ⟨ledger, saved, hout⟩ := collectionRecord_output rate rewards C_star C_h v ⟨z, hcol⟩
        have hadj := congrArg ReferenceActivePhysicalStep.State.coordinator
          (actualRecord_adjacent rate rewards C_star C_h v d hvd z _ _ hvR
            (cutoff_record rate rewards C_star C_h e n z hz))
        obtain ⟨he, r, owned, base, hin, _⟩ := collectionPrefixCell_live rate rewards C_star C_h e n z hz
        rw [hin, hout] at hadj
        cases hadj
    have hstate' : noncallCalendar rate rewards C_star C_h t z a initial (v.val + 1) = some state := by
      have hindex : v.val + 1 = start z + e := hvd
      rw [hindex]
      exact hstate
    obtain ⟨prev, _hprev, _hncall, happend⟩ :=
      noncallCalendar_some_succ rate rewards C_star C_h t v z a initial state hlt hstate'
    rw [happend, appendNoncallDate, noncallDateCell, dite_eq_left hlive]
    change (continuingLogicalCell rate rewards C_star C_h v ⟨z, hlive⟩ a).nextSlowSet = _
    have hn := continuingLogicalCell_word rate rewards C_star C_h v ⟨z, hlive⟩ a
    have hbefore : continuingBefore rate rewards C_star C_h v ⟨z, hlive⟩ =
        collectionState rate rewards C_star C_h e n z hz (e - 1) := by
      simp only [collectionState, continuingBefore, continuingNumericalWord, collectionWord, hi]
    obtain ⟨hbound, hnum, _⟩ := hn.2.2.2
    have hinput : (continuingSourceCell rate rewards C_star C_h v ⟨z, hlive⟩).input =
        triggerInput rate rewards C_star C_h e n z hz := by
      apply numericalCoordinates_injective
      simpa only [continuingLogicalCell, appendLogicalCell, triggerInput,
        continuingNumericalWord, collectionWord, hi,
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates] using hnum
    have hclear : (continuingBefore rate rewards C_star C_h v ⟨z, hlive⟩).overflow = false := by
      rw [hbefore]
      exact clear_before rate rewards C_star C_h e n z hz (e - 1) (by omega)
    have hcallS : NoCallBetween rate rewards C_star C_h t v.castSucc s.val := by
      intro r htr hrv
      have hh := hcall r htr (by change r.val < q.val; change r.val < v.val at hrv; omega)
      simpa only [hs] using hh
    have hpay := firstInvocation_continuingPayload rate rewards C_star C_h t v s hlt hcallS
      (by simpa only [hs] using hlive)
    have hpay' : (continuingSourceCell rate rewards C_star C_h v ⟨z, hlive⟩).selected.view.payload = P := by
      have hx : (⟨s.val, by simpa only [hs] using hlive⟩ : ContinuingLiveSource rate rewards C_star C_h v) =
          ⟨z, hlive⟩ := Subtype.ext hs
      exact (congrArg (fun x : ContinuingLiveSource rate rewards C_star C_h v =>
        (continuingSourceCell rate rewards C_star C_h v x).selected.view.payload) hx).symm.trans
          (hpay.trans hP.symm)
    rw [continuingLogicalCell, native_trigger_next rate _ _ _ _ hclear
      (hbit _ (continuingSourceCell_spec rate rewards C_star C_h v ⟨z, hlive⟩).1)]
    rw [hbefore, hinput, hpay', evaluatorArray_other_date b t a (v, 1) heq]
    rw [continuingRecord_time rate rewards C_star C_h v ⟨z, hlive⟩]
    rfl

private theorem generated_window_recurrence
    (control0 : ContinuousLearningRows.TimeControl p) (b : Bool) (u t q : Fin p.T)
    (htq : t.val < q.val) (s : FirstSource t) (hs : s.val = z)
    (hc : s.val ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t)
    (hdate : start z + n = q.val)
    (hcall : NoCallBetween rate rewards C_star C_h t q.castSucc z)
    (a : Auxiliary p) (H : List (LogicalCell p rate)) :
    (noncallCalendar rate rewards C_star C_h t z a
      ((actualFirstCell rate rewards C_star C_h control0 t s (a (t, if b then 0 else 1))).nextSlowSet, H)
      q.val).map Prod.fst =
      some (sampledArrayPath rate rewards C_star C_h e n z hz (n - e) le_rfl
        (evaluatorArray b t a) (Fin.last (n - e))) := by
  let initial := ((actualFirstCell rate rewards C_star C_h control0 t s
    (a (t, if b then 0 else 1))).nextSlowSet, H)
  let D := sampledArrayPath rate rewards C_star C_h e n z hz (n - e) le_rfl (evaluatorArray b t a)
  have hafter := produced_before_cutoff rate rewards C_star C_h e n z hz t q htq s hs hdate
  have heb := hz.1
  have hP := oldPayload_eq_produced rate rewards C_star C_h e n z hz t q htq s hs hdate hcall
  have hinit := trigger_initialization rate rewards C_star C_h e n z hz control0 b u t q htq s hs hc hdate hcall a H
  have hzero : ∃ state, noncallCalendar rate rewards C_star C_h t z a initial (start z + e) = some state ∧
      state.1 = D 0 := by
    cases hr : noncallCalendar rate rewards C_star C_h t z a initial (start z + e) with
    | none => rw [hr, Option.map_none] at hinit; cases hinit
    | some state =>
        rw [hr, Option.map_some] at hinit
        exact ⟨state, rfl, Option.some.inj hinit⟩
  have hrec : ∀ k (hk : k ≤ n - e),
      ∃ state, noncallCalendar rate rewards C_star C_h t z a initial (start z + e + k) = some state ∧
        state.1 = D ⟨k, by omega⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact hzero
    | succ k ih =>
        intro hk
        obtain ⟨state, hrun, hseed⟩ := ih (by omega)
        let v : Fin p.T := ⟨start z + e + k, by have := q.isLt; omega⟩
        have htv : t.val < v.val := by dsimp only [v]; omega
        have hvq : v.val < q.val := by dsimp only [v]; omega
        have hnocall := hcall v htv hvq
        have hcol : z ∈ colDomain v :=
          window_collection_domain rate rewards C_star C_h e n z hz t q htq s hs hdate hcall k (by omega)
        have hidx : v.val - start z = e + k := by dsimp only [v]; omega
        have hbefore : collectionBefore rate rewards C_star C_h v ⟨z, hcol⟩ =
            collectionState rate rewards C_star C_h e n z hz (e + k) := by
          simp only [collectionBefore, collectionNumericalWord, collectionState, collectionWord, hidx]
        obtain ⟨hbound, _hstart, hinput0⟩ := collectionInput_word rate rewards C_star C_h v ⟨z, hcol⟩
        have hinput : collectionInput rate rewards C_star C_h v ⟨z, hcol⟩ =
            windowInput rate rewards C_star C_h e n z hz ⟨k, by omega⟩ := by
          simpa only [collectionNumericalWord, collectionWord, windowInput, hidx] using hinput0
        have hcallS : NoCallBetween rate rewards C_star C_h t v.castSucc s.val := by
          intro r htr hrv
          have hh := hcall r htr (by change r.val < q.val; change r.val < v.val at hrv; omega)
          simpa only [hs] using hh
        have hcolS : s.val ∈ colDomain v := by simpa only [hs] using hcol
        have hpayS := firstInvocation_collectionPayload rate rewards C_star C_h t v s htv hcallS hcolS
        have hpay : (collectionArguments rate rewards C_star C_h v ⟨z, hcol⟩).1 = P := by
          have hx : (⟨s.val, hcolS⟩ : CollectionDateSource rate rewards C_star C_h v) = ⟨z, hcol⟩ := Subtype.ext hs
          exact (congrArg (fun x : CollectionDateSource rate rewards C_star C_h v =>
            (collectionArguments rate rewards C_star C_h v x).1) hx).symm.trans (hpayS.trans hP.symm)
        have hclear : (collectionBefore rate rewards C_star C_h v ⟨z, hcol⟩).overflow = false := by
          rw [hbefore]
          exact clear_before rate rewards C_star C_h e n z hz (e + k) (by omega)
        have hstep := appendNoncallDate_collection_refresh rate rewards C_star C_h z v hcol a state hclear
        rw [hbefore, hinput, hpay, hseed] at hstep
        have hD : D ⟨k + 1, by omega⟩ =
            DeferredRefreshUniformKernels.sampleRecordedRefresh p Q
              (collectionState rate rewards C_star C_h e n z hz (e + k))
              (windowInput rate rewards C_star C_h e n z hz ⟨k, by omega⟩)
              (P).anchor (P).anchor_pos (D ⟨k, by omega⟩) (a (v, 0), a (v, 1)) := by
          change sampledPath rate rewards C_star C_h e n z hz (n - e) le_rfl
            (actualPrefixCoordinates rate rewards C_star C_h e n ⟨z, hz⟩ (n - e) le_rfl
              (evaluatorArray b t a)) (⟨k, by omega⟩ : Fin (n - e)).succ = _
          rw [sampledPath_succ]
          have haddr0 : actualCoordinateIndex rate rewards C_star C_h e n z hz (n - e) le_rfl
              (.inr (.inl ⟨k, by omega⟩)) = (v, 0) := by
            apply Prod.ext
            · exact Fin.ext (actualCoordinateIndex_step rate rewards C_star C_h e n z hz _ _ ⟨k, by omega⟩).1
            · exact (actualCoordinateIndex_step rate rewards C_star C_h e n z hz _ _ ⟨k, by omega⟩).2.1
          have haddr1 : actualCoordinateIndex rate rewards C_star C_h e n z hz (n - e) le_rfl
              (.inr (.inr ⟨k, by omega⟩)) = (v, 1) := by
            apply Prod.ext
            · exact Fin.ext (actualCoordinateIndex_step rate rewards C_star C_h e n z hz _ _ ⟨k, by omega⟩).2.2.1
            · exact (actualCoordinateIndex_step rate rewards C_star C_h e n z hz _ _ ⟨k, by omega⟩).2.2.2
          dsimp only [actualPrefixCoordinates]
          rw [haddr0, haddr1, evaluatorArray_other_date b t a (v, 0) (Fin.ne_of_gt htv),
            evaluatorArray_other_date b t a (v, 1) (Fin.ne_of_gt htv)]
          rfl
        refine ⟨appendNoncallDate rate rewards C_star C_h v z a state, ?_, hstep.trans hD.symm⟩
        have hindex : start z + e + (k + 1) = (start z + e + k) + 1 := by omega
        rw [hindex, noncallCalendar, hrun, Option.bind_some,
          dite_eq_left ⟨htv, v.isLt⟩, ite_eq_left hnocall]
  obtain ⟨state, hrun, hseed⟩ := hrec (n - e) le_rfl
  have hindex : start z + e + (n - e) = q.val := by omega
  rw [hindex] at hrun
  rw [hrun, Option.map_some]
  exact congrArg some hseed

private theorem producedSource_callCell (b : Bool) (u t : Fin p.T)
    (w : BranchLift rate rewards C_star C_h b u t) :
    (producedSource rate rewards C_star C_h b u t w).val ∈
      ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u t := by
  cases b
  · exact firstCall_insertVector_mem rate rewards C_star C_h u t w.1.1.val w.1.1.property.1 w.2
  · exact (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t w).2.property.1

/-- The retained generated PRE endpoint at the immediate next actual
nonrenewed invocation is the canonical old-anchor path on the same inserted
source, using an injective view of the same original auxiliary array.

The only branch tests are absence of intervening actual invocations, presence
of this nonrenewed actual call, and its computed PRE numerical clear flag.
The whole array and generated list remain the original observations. -/
theorem retained_endpoint
    (control0 : ContinuousLearningRows.TimeControl p) (b : Bool) (u t q : Fin p.T)
    (htq : t.val < q.val) (w : BranchLift rate rewards C_star C_h b u t)
    (hbetween : NoCallBetween rate rewards C_star C_h t q.castSucc
      (insertedPhysicalSource rate (branchTransition rate rewards C_star C_h control0 b u t w)))
    (hcall : ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall
      rate rewards C_star C_h q
      (insertedPhysicalSource rate (branchTransition rate rewards C_star C_h control0 b u t w)))
    (hclear : ∃ o, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h q.val
        (insertedPhysicalSource rate (branchTransition rate rewards C_star C_h control0 b u t w)) = some o ∧
      o.2.1 = false) :
    let z := insertedPhysicalSource rate (branchTransition rate rewards C_star C_h control0 b u t w)
    ∃ (e n : ℕ) (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
      (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e n),
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q z = some (cutoff, theta) ∧
      physicalStart rate z rewards C_star C_h + n = q.val ∧
      theta.1 = (RecordedCorrectedWindow.actualPrefixSamplerMass p (queueParameters rate)
        (ReferenceActualCollectionNonrenewedEndpointFibreJoin.collectionQueue_sourceCap rate)
        (collectionWord rate rewards C_star C_h e n z hz) e n
        (collectionPrefixCell_trigger_positive rate rewards C_star C_h e n z hz)
        hz.1 (collectionWord_bound rate rewards C_star C_h e n z hz)).weight ∧
      theta.2 = (oldPayload rate rewards C_star C_h e n z hz).anchor ∧
      oldPayload rate rewards C_star C_h e n z hz =
        (firstCell t (producedSource rate rewards C_star C_h b u t w)).selected.view.payload ∧
      prefixNumerical rate rewards C_star C_h q.castSucc z =
        some (collectionState rate rewards C_star C_h e n z hz n) ∧
      t.val ≤ physicalStart rate z rewards C_star C_h + e - 1 ∧
      ((branchObservation rate rewards C_star C_h control0 b u t q.castSucc w).2.2.2).map Prod.fst =
        some (sampledArrayPath rate rewards C_star C_h e n z hz (n - e) le_rfl
          (evaluatorArray b t w.1.2) (Fin.last (n - e))) ∧
      Function.Injective (consumedAddress rate rewards C_star C_h e n z hz b t (n - e) le_rfl) ∧
      ∀ i, let j := consumedAddress rate rewards C_star C_h e n z hz b t (n - e) le_rfl i
        t.val < j.1.val ∨ (j.1 = t ∧ j.2 = if b then 0 else 1) := by
  dsimp only
  let d := branchTransition rate rewards C_star C_h control0 b u t w
  let z := insertedPhysicalSource rate d
  let s := producedSource rate rewards C_star C_h b u t w
  have hs : s.val = z := producedSource_val rate rewards C_star C_h control0 b u t w
  obtain ⟨e, n, record, cutoff, theta, hz, _hr, hcallAt, hdate, hweight, hanchor⟩ :=
    ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall_parameters
      rate rewards C_star C_h q z hcall hclear
  have hafter := produced_before_cutoff rate rewards C_star C_h e n z hz t q htq s hs hdate
  have htrigger : t.val ≤ start z + e - 1 := by omega
  have hpay := oldPayload_eq_produced rate rewards C_star C_h e n z hz t q htq s hs hdate hbetween
  have hword := prefixNumerical_actualWord rate rewards C_star C_h q.castSucc z
    (collectionPrefixCell_launch rate rewards C_star C_h e n z hz) (by change start z ≤ q.val; omega)
  have hidx : q.val - start z = n := by omega
  have hnum : prefixNumerical rate rewards C_star C_h q.castSucc z =
      some (collectionState rate rewards C_star C_h e n z hz n) := by
    simpa only [Fin.val_castSucc, collectionState, collectionWord, hidx] using hword
  have hgen := generated_window_recurrence rate rewards C_star C_h e n z hz control0 b u t q htq s hs
    (producedSource_callCell rate rewards C_star C_h b u t w) hdate hbetween w.1.2 (postHistory d)
  have hseed : postSeed rate d =
      (actualFirstCell rate rewards C_star C_h control0 t s (w.1.2 (t, if b then 0 else 1))).nextSlowSet :=
    congrArg LogicalCell.nextSlowSet (produced_cell rate rewards C_star C_h control0 b u t w)
  have hobs : (branchObservation rate rewards C_star C_h control0 b u t q.castSucc w).2.2.2 =
      noncallCalendar rate rewards C_star C_h t z w.1.2 (postSeed rate d, postHistory d) q.val := by
    cases b <;> rfl
  refine ⟨e, n, cutoff, theta, hz, hcallAt, hdate, hweight, hanchor, hpay, hnum, htrigger, ?_,
    consumedAddress_injective rate rewards C_star C_h e n z hz b t (n - e) le_rfl, ?_⟩
  · rw [hobs, hseed]
    exact hgen
  · exact consumedAddress_unused rate rewards C_star C_h e n z hz b t htrigger (n - e) le_rfl

end Bandits.Support.ReferencePostInvocationRetainedEndpointRecurrence
