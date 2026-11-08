/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInvocationCallSplice

import Mathlib.Tactic

/-!
# Actual native invocation geometry and retained endpoint recurrence

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.

These internal pointwise lemmas use the actual invocation, complete physical
records and complete original numerical word at any native rank. Installation
and episode-anchor identities require only actual selector presence. Payload
retention requires the actual intervening no-call interval. LIVE-seed agreement
also retains its explicit noncall-run, numerical PRE-clear and LIVE premises.
The retained endpoint requires the actual nonrenewed call and PRE-clear readout;
it includes a trigger at the native origin and the renewal label swap.

No generated calendar, produced-law factorization, endpoint distribution,
source-marginal preservation or manuscript closure is asserted here.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInstallationCellFactors
open ReferenceFirstCollectionLogicalNumericalAlignment (originalWord_record_map)
open ReferencePostInvocationNoncallGeometry
open ReferenceActualCollectionHiddenRefreshPath (actualOriginalWord)
open ReferenceFirstLaunchNumericalCell (queueParameters)
open ReferenceCompletePhysicalHistory (physicalStart completeSuffixRecords)
open ReferenceFirstCollectionLogicalPrefixExtension (noCallAt)

open RecordedQueueRun (RoundInput RunState run)
open ReferenceActivePhysicalStep (Payload)
open ReferenceCompleteLaterLiveComplementPrefixReplay (continuingTest)
open ReferenceAssignmentPayloadPersistence (InstallationBirth storedPayload storedPayload_live)
open ReferenceFirstCorrectedNextCalendarWordJoin (calendarReplay)
open ReferenceLaterCollectionArrivalReadout
  (laterCollectionReadout laterCollectionReadout_domain)
open CoordinatorLiveChoiceRecorderStep (Registers)
open ReferenceSourcePrefixHistoryFiltration (actualRecord)
open FollowerCutoffScan (gridBoundary completeRowProposalBit)
open ReferenceFirstCollectionCurrentRetainedGate (cell0)
open ReferenceCorrectedInitializationLaunch (correctedLaunch)
open ReferenceCompletePhysicalHistory (completeSuffixRecords_length)
open ReferenceActualCollectionHiddenRefreshPath (actualOriginalWord_length actualOriginalWord_spec)

open ReferenceGeneratedInvocationCallSplice
open ReferencePostInvocationGeneratedAlignment

namespace Bandits.Support.ReferenceGeneratedNativeInvocationGeometry

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "PhysicalRecord" => ReferenceFirstLiveChronologicalPrefixFoundation.Record rate
local notation "Q" => queueParameters rate
local notation "start " z:max => physicalStart rate z rewards C_star C_h
local notation "records " z:max => completeSuffixRecords rate z rewards C_star C_h
local notation "NativeSource" => InvocationSource rate rewards C_star C_h
local notation "LiveSource" => ContinuingLiveSource rate rewards C_star C_h
local notation "liveCell" => continuingSourceCell rate rewards C_star C_h
local notation "liveRecord" => continuingRecord rate rewards C_star C_h
local notation "collectionRecordAt" => collectionRecord rate rewards C_star C_h
local notation "collectionArgs" => collectionArguments rate rewards C_star C_h
local notation "livePRE" => continuingBefore rate rewards C_star C_h
local notation "originalWord" => actualOriginalWord rate rewards C_star C_h
local notation "sourceRecord" => actualRecord rate rewards C_star C_h
local notation "CallFree" => NoCallBetween rate rewards C_star C_h
local notation "noncallRun" => noncallCalendar rate rewards C_star C_h
local notation "liveDomain" => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h
local notation "collectionDomain" => collectionDateDomain rate rewards C_star C_h

local notation "AuxiliaryArray" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "FullVector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "TimeControls" => ContinuousLearningRows.TimeControl p
local notation "UniformScalar" => ContinuousControlSlice.Scalar
local notation "Cell" => LogicalCell p rate
local notation "insertVector" => ReferenceFirstCollectionRenewalVectorInsertion.insert
local notation "nativeCellAt" => nativeCell rate rewards C_star C_h
local notation "nativeBeforeAt" => nativeBefore rate rewards C_star C_h
local notation "nativeSourceAt" => nativeSourceCell rate rewards C_star C_h
local notation "nativeRecordAt" => nativeRecord rate rewards C_star C_h
local notation "rankAt" => nativeRank rate rewards C_star C_h
local notation "numericalAt" => prefixNumerical rate rewards C_star C_h
local notation "sourceCall" => ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h

/-- Every actual invocation, including later invocations, supplies its native
installation and birth on this source's complete record list. -/
theorem nativeInvocation_installation (t : Fin p.T) (z : NativeSource t) :
    ∃ (b : Fin (records z.val).length) (rb : Registers p rate.eta)
      (qb : CoordinatorLiveServiceFinish.OwnedRegisters rb) (beta : Fin (p.m - 1) → ℕ),
      sourceRecord t z.val = some (records z.val)[b.val] ∧ (records z.val)[b.val] = nativeRecordAt t z ∧
      ReferenceCollectionPhaseHistory.laterChosen (records z.val)[b.val].input = true ∧
      (records z.val)[b.val].output.next.coordinator = .live rb qb beta ∧
      InstallationBirth (records z.val)[b.val] rb.payload ∧
      rb.payload = (nativeSourceAt t z).selected.view.payload := by
  obtain ⟨b, hr, _ht, hb⟩ := ReferenceRankInstallationRecorderFoundation.installationEvent_chosen
      rate rewards C_star C_h (rankAt t z.val) t z.val (native_installation rate rewards C_star C_h t z)
  have heq : (records z.val)[b.val] = nativeRecordAt t z :=
    Option.some.inj (hr.symm.trans (nativeSourceCell_spec rate rewards C_star C_h t z).1)
  obtain ⟨_P0, rb, qb, beta, _cell, native, _hlen, _hmap, _hprefix, _hinit,
      hnext, hbirth, _hsigma, _hbase, _hcell, _hinput, hpayload, _⟩ :=
    ReferenceCompleteInstallationCollectionPrefixNumericalTruth.actual_later_installation_collection_prefix_numerical_truth
      rate rewards C_star C_h z.val b hb
  have hselected : ((records z.val)[b.val].output.preparation.coordinator.selection).map
        (fun s => s.view.payload) = some rb.payload := by
    rw [native.selection_actual, Option.map_some, hpayload]
  rw [heq, (nativeSourceAt t z).selection_actual, Option.map_some] at hselected
  exact ⟨b, rb, qb, beta, hr, heq, hb, hnext, hbirth, (Option.some.inj hselected).symm⟩

private theorem continuing_not_birth (r : PhysicalRecord) (htest : continuingTest r = true) (P : Payload rate) :
    ¬ InstallationBirth r P := by
  intro hbirth
  cases hp : r.output.preparation.coordinator <;>
    simp_all only [continuingTest, InstallationBirth, Bool.false_eq_true]

private theorem collection_not_birth (r : PhysicalRecord) (c : RoundInput p.K)
    (hc : laterCollectionReadout 0 r = some c) (P : Payload rate) : ¬ InstallationBirth r P := by
  intro hbirth
  have hphase := ((laterCollectionReadout_domain 0 r).mp (by rw [hc]; rfl)).2
  cases hp : r.output.preparation.coordinator with
  | first outcome => cases outcome <;> simp only [hp] at hphase
  | live regs owned base outcome =>
      simp only [InstallationBirth, hp] at hbirth
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [hp, InstallationBirth] at hphase hbirth
  | invalidCollectionCutoff => simp only [hp] at hphase
  | dagger => simp only [hp] at hphase

/-- Actual POST-t payload retention through the PRE boundary, and no births strictly before it. -/
theorem nativeInvocation_retained_interval (t : Fin p.T) (n : Fin (p.T + 1)) (z : NativeSource t)
    (hcall : CallFree t n z.val) :
    (∀ v : Fin p.T, t.val < v.val → v.val ≤ n.val → ∀ r : PhysicalRecord, sourceRecord v z.val = some r →
        storedPayload r.input.state.coordinator = some ((nativeSourceAt t z).selected.view.payload)) ∧
    (∀ v : Fin p.T, t.val < v.val → v.val < n.val → ∀ r : PhysicalRecord, sourceRecord v z.val = some r →
        ∀ fresh, ¬ InstallationBirth r fresh) := by
  obtain ⟨b, rb, _qb, _beta, hr, _heq, _hb, hnext, _hbirth, hpay⟩ :=
    nativeInvocation_installation rate rewards C_star C_h t z
  have hst := (actualRecord_index rate rewards C_star C_h t z.val _ hr).choose_spec.2.2
  constructor
  · intro v htv hvn r hrecord
    have hp := noCallBetween_payload rate rewards C_star C_h t n z.val hst hcall v htv hvn
    rw [ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?, hrecord,
      Option.bind_some, hr, Option.bind_some, hnext, storedPayload_live, hpay] at hp
    exact hp
  · intro v htv hvn r hrecord fresh
    rcases noncall_phase_coverage rate rewards C_star C_h v z.val (by omega)
      (hcall v htv hvn) with hlive | hcollection
    · have heq : r = liveRecord v ⟨z.val, hlive⟩ :=
        Option.some.inj (hrecord.symm.trans (continuingSourceCell_spec rate rewards C_star C_h v ⟨z.val, hlive⟩).1)
      rw [heq]
      exact continuing_not_birth rate _
        (continuingRecord_frame rate rewards C_star C_h v ⟨z.val, hlive⟩).choose_spec.choose_spec.choose_spec.choose_spec.2.1 fresh
    · have heq : r = collectionRecordAt v ⟨z.val, hcollection⟩ :=
        Option.some.inj (hrecord.symm.trans (collectionRecord_spec rate rewards C_star C_h v ⟨z.val, hcollection⟩).1)
      rw [heq]
      exact collection_not_birth rate _ _
        (collectionInput_readout rate rewards C_star C_h v ⟨z.val, hcollection⟩) fresh

/-- Actual collection retains the installed POST-t payload, with an evolving logical set. -/
theorem nativeInvocation_collectionPayload (t q : Fin p.T) (z : NativeSource t) (htq : t.val < q.val)
    (hcall : CallFree t q.castSucc z.val) (hc : z.val ∈ collectionDomain q) :
    (collectionArgs q ⟨z.val, hc⟩).1 = (nativeSourceAt t z).selected.view.payload := by
  have hr := (collectionRecord_spec rate rewards C_star C_h q ⟨z.val, hc⟩).1
  have hp := (nativeInvocation_retained_interval rate rewards C_star C_h t q.castSucc z hcall).1 q htq le_rfl _ hr
  have hi := collectionArguments_incoming rate rewards C_star C_h q ⟨z.val, hc⟩
  rw [ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?, hr, Option.bind_some] at hi
  exact Option.some.inj (hi.symm.trans hp)

/-- The selected LIVE payload retains its actual installation origin. -/
theorem nativeInvocation_continuingPayload (t q : Fin p.T) (z : NativeSource t) (htq : t.val < q.val)
    (hcall : CallFree t q.castSucc z.val) (hlive : z.val ∈ liveDomain q) :
    (liveCell q ⟨z.val, hlive⟩).selected.view.payload = (nativeSourceAt t z).selected.view.payload := by
  obtain ⟨regs, owned, base, _started, hin, _htest, hpay, _⟩ :=
    continuingRecord_frame rate rewards C_star C_h q ⟨z.val, hlive⟩
  have hp := (nativeInvocation_retained_interval rate rewards C_star C_h t q.castSucc z hcall).1
    q htq le_rfl _ (continuingSourceCell_spec rate rewards C_star C_h q ⟨z.val, hlive⟩).1
  rw [hin, storedPayload_live] at hp
  exact hpay.trans (Option.some.inj hp)

/-- A real invocation supplies its own corrected launch, at every rank. -/
theorem nativeInvocation_launch (t : Fin p.T) (z : NativeSource t) :
    ∃ active, correctedLaunch rate z.val rewards C_star C_h = some active := by
  cases hl : correctedLaunch rate z.val rewards C_star C_h with
  | some active => exact ⟨active, rfl⟩
  | none =>
      have hnil := (ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
        rate rewards C_star C_h z.val hl).1
      have hi := (nativeRecordIndex rate rewards C_star C_h t z).isLt
      have hlen : (records z.val).length = 0 := congrArg List.length hnil
      omega

/-- The installed old anchor is its actual episode-origin weight vector on the complete word. -/
theorem nativeInvocation_episode_anchor (t : Fin p.T) (z : NativeSource t) :
    let R := records z.val
    let P := (nativeSourceAt t z).selected.view.payload
    let W := originalWord z.val (nativeInvocation_launch rate rewards C_star C_h t z)
    ∃ (b rho : Fin R.length) (P_rho : Payload rate), sourceRecord t z.val = some R[b.val] ∧
      InstallationBirth R[b.val] P ∧ rho.val ≤ b.val ∧ InstallationBirth R[rho.val] P_rho ∧
      ReferenceCompleteEpisodeAnchorOrigin.IsEpisodeAnchorBirth R[rho.val] ∧ P.anchor = P_rho.anchor ∧
      (∀ j, P_rho.anchor j = AssignmentScoreReconstruction.sourceWeightBase p ^
        (calendarReplay rate W j rho.val).1) ∧
      R[rho.val].input.time = P_rho.sigma ∧ P_rho.sigma.val ≤ P.sigma.val ∧
      gridBoundary p rate.eta.val P_rho.sigma = gridBoundary p rate.eta.val P.sigma := by
  dsimp only
  obtain ⟨b, rb, _qb, _beta, hr, _heq, _hb, _hnext, hbirth, hpay⟩ :=
    nativeInvocation_installation rate rewards C_star C_h t z
  rw [hpay] at hbirth
  have hrestore := ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
    rate rewards C_star C_h z.val
  rw [Classical.choose_spec (nativeInvocation_launch rate rewards C_star C_h t z)] at hrestore
  obtain ⟨whole, _hlen, _hprefix, hfull, _hunique, hbirths, _hbranches, _hweights⟩ := hrestore
  have hwhole : whole = originalWord z.val (nativeInvocation_launch rate rewards C_star C_h t z) :=
    Option.some.inj (hfull.symm.trans (actualOriginalWord_spec rate rewards C_star C_h z.val _))
  obtain ⟨rho, P_rho, hrho, hroot, hepisode, _hcurrent, _horigin, hanchor,
    hpow, htime, htimeOrder, hgrid, _hspan⟩ := hbirths b _ hbirth
  exact ⟨b, rho, P_rho, hr, hbirth, hrho, hroot, hepisode, hanchor,
    by simpa only [hwhole] using hpow, htime, htimeOrder, hgrid⟩

private theorem prefix_clear_mono (W : List (RoundInput p.K)) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ W.length)
    (hclear : (run Q (W.take j)).overflow = false) : (run Q (W.take i)).overflow = false := by
  cases hi : (run Q (W.take i)).overflow with
  | false => rfl
  | true =>
      have hfirst := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q W i (hij.trans hj)).mp hi
      have hlate := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q W j hj).mpr (hfirst.trans hij)
      rw [hclear] at hlate
      cases hlate

private theorem appendLogicalCell_next_of_noProposal (r : PhysicalRecord)
    (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r) (S : RunState p.K)
    (a : AuxiliaryArray) (hclear : S.overflow = false)
    (hbit : completeRowProposalBit p rate.eta.val r.input.row r.input.time = false) :
    (appendLogicalCell r c S a).nextSlowSet = c.selected.view.payload.slowSet := by
  simp only [appendLogicalCell, hclear, hbit, Bool.not_false, Bool.true_and, Bool.false_eq_true, ite_false]

private theorem previous_record_proposal_false (v q : Fin p.T)
    (hvq : v.val + 1 = q.val) (z : LiveSource q) (r : PhysicalRecord) (hr : sourceRecord v z.val = some r) :
    completeRowProposalBit p rate.eta.val r.input.row r.input.time = false := by
  have hb := continuing_previous_proposal_false rate rewards C_star C_h q z v hvq
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h v z.val r hr
  simpa only [ReferenceActivePhysicalStep.RoundInput.row, hf.1, hf.2.1, hf.2.2.1] using hb

/-- Native PRE is the stopped replay of the complete word on its own source. -/
theorem nativeCell_before_word (control0 : TimeControls) (t : Fin p.T)
    (z : NativeSource t) (x : UniformScalar) : (nativeCellAt control0 t z x).before =
      run Q ((originalWord z.val (nativeInvocation_launch rate rewards C_star C_h t z)).take
        (t.val - start z.val)) := by
  have hst := (actualRecord_index rate rewards C_star C_h t z.val _
    (nativeSourceCell_spec rate rewards C_star C_h t z).1).choose_spec.2.2
  change nativeBeforeAt control0 t z = _
  exact Option.some.inj ((nativeBefore_prefix rate rewards C_star C_h control0 t z).symm.trans
    (prefixNumerical_actualWord rate rewards C_star C_h t.castSucc z.val
      (nativeInvocation_launch rate rewards C_star C_h t z) hst))

/-- A native-origin surviving calendar has the actual LIVE seed before
overflow. The supplied list is arbitrary here: this seed fact does not use
list order. The boundary includes the immediate successor of the invocation. -/
theorem nativeInvocation_generated_live_seed (control0 : TimeControls)
    (t q : Fin p.T) (z : NativeSource t) (htq : t.val < q.val) (a : AuxiliaryArray)
    (x : UniformScalar) (L : List Cell) (s : SlowSet p × List Cell) (S : RunState p.K)
    (hs : noncallRun t z.val a ((nativeCellAt control0 t z x).nextSlowSet,
        L ++ [nativeCellAt control0 t z x]) q.val = some s) (hS : numericalAt q.castSucc z.val = some S)
    (hclearS : S.overflow = false) (hlive : z.val ∈ liveDomain q) :
    s.1 = (liveCell q ⟨z.val, hlive⟩).selected.view.payload.slowSet := by
  let W := originalWord z.val (nativeInvocation_launch rate rewards C_star C_h t z)
  have hst := (actualRecord_index rate rewards C_star C_h t z.val _
    (nativeSourceCell_spec rate rewards C_star C_h t z).1).choose_spec.2.2
  have hWlen : W.length = p.T - start z.val := by
    rw [actualOriginalWord_length, completeSuffixRecords_length]
  have hqW : q.val - start z.val ≤ W.length := by rw [hWlen]; omega
  have hstate : S = run Q (W.take (q.val - start z.val)) := Option.some.inj (hS.symm.trans
      (prefixNumerical_actualWord rate rewards C_star C_h q.castSucc z.val
        (nativeInvocation_launch rate rewards C_star C_h t z) (by
          change start z.val ≤ q.val
          omega)))
  have hclear : (run Q (W.take (q.val - start z.val))).overflow = false := by
    rw [← hstate]
    exact hclearS
  have hcall : CallFree t q.castSucc z.val := by
    apply (noncallCalendar_isSome rate rewards C_star C_h t q.castSucc z.val a
      ((nativeCellAt control0 t z x).nextSlowSet, L ++ [nativeCellAt control0 t z x])).mp
    change (noncallRun t z.val a _ q.val).isSome = true
    rw [hs]
    rfl
  have hpay := nativeInvocation_continuingPayload rate rewards C_star C_h t q z htq hcall hlive
  by_cases hfirst : q.val = t.val + 1
  · have hinit := noncallCalendar_initial rate rewards C_star C_h t z.val a
      ((nativeCellAt control0 t z x).nextSlowSet, L ++ [nativeCellAt control0 t z x]) q.val (by omega)
    have heq := Option.some.inj (hs.symm.trans hinit)
    rw [heq]
    have hbefore : (nativeBeforeAt control0 t z).overflow = false := by
      change (nativeCellAt control0 t z x).before.overflow = false
      rw [nativeCell_before_word rate rewards C_star C_h control0 t z x]
      exact prefix_clear_mono rate W (t.val - start z.val) (q.val - start z.val) (by omega) hqW hclear
    have hbit := previous_record_proposal_false rate rewards C_star C_h t q hfirst.symm
      ⟨z.val, hlive⟩ (nativeRecordAt t z) (nativeSourceCell_spec rate rewards C_star C_h t z).1
    exact (appendLogicalCell_next_of_noProposal rate _ _ _ _ hbefore hbit).trans
      (congrArg (fun P => P.slowSet) hpay.symm)
  · let v : Fin p.T := ⟨q.val - 1, by omega⟩
    have hvq : v.val + 1 = q.val := by dsimp only [v]; omega
    have htv : t.val < v.val := by dsimp only [v]; omega
    have hs' : noncallRun t z.val a ((nativeCellAt control0 t z x).nextSlowSet,
          L ++ [nativeCellAt control0 t z x]) (v.val + 1) = some s := by simpa only [hvq] using hs
    obtain ⟨prev, _hprev, hnocall, happend⟩ :=
      noncallCalendar_some_succ rate rewards C_star C_h t v z.val a _ s htv hs'
    have hvLive := continuing_previous_domain rate rewards C_star C_h v q hvq
      ⟨z.val, hlive⟩ (by change start z.val < v.val; omega) hnocall
    have hcell : noncallDateCell rate rewards C_star C_h v z.val a prev.1 =
        some (continuingLogicalCell rate rewards C_star C_h v ⟨z.val, hvLive⟩ a) := by
      rw [noncallDateCell, dite_eq_left hvLive]
    rw [happend, appendNoncallDate, hcell]
    have hvclear : (livePRE v ⟨z.val, hvLive⟩).overflow = false :=
      prefix_clear_mono rate W (v.val - start z.val) (q.val - start z.val) (by omega) hqW hclear
    have hbit := previous_record_proposal_false rate rewards C_star C_h v q hvq
      ⟨z.val, hlive⟩ (liveRecord v ⟨z.val, hvLive⟩)
      (continuingSourceCell_spec rate rewards C_star C_h v ⟨z.val, hvLive⟩).1
    have hcallv : CallFree t v.castSucc z.val := by
      intro r htr hrv
      exact hcall r htr (by
        change r.val < q.val
        change r.val < v.val at hrv
        omega)
    have hpayv := nativeInvocation_continuingPayload rate rewards C_star C_h t v z htv hcallv hvLive
    exact (appendLogicalCell_next_of_noProposal rate _ _ _ a hvclear hbit).trans
      (congrArg (fun P => P.slowSet) (hpayv.trans hpay.symm))

/-- Actual invocation count before a calendar boundary, including the
terminal boundary. This is a readout of the source, never carried as state. -/
def boundaryCallCount (n : Fin (p.T + 1)) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  (Finset.univ.filter (fun v : Fin p.T => v.val < n.val ∧ (sourceCall v z).isSome)).card

theorem boundaryCallCount_castSucc (q : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    boundaryCallCount rate rewards C_star C_h q.castSucc z = rankAt q z := rfl

/-- Split the actual dates into those before s, the call at s, and the
call-free interval after s. Failed sampler outcomes still count at s. -/
theorem boundaryCallCount_native_interval (s : Fin p.T) (n : Fin (p.T + 1))
    (z : NativeSource s) (hsn : s.val < n.val) (hcall : CallFree s n z.val) :
    boundaryCallCount rate rewards C_star C_h n z.val = rankAt s z.val + 1 := by
  let before := Finset.univ.filter (fun v : Fin p.T => v.val < s.val ∧ (sourceCall v z.val).isSome)
  have hdates : Finset.univ.filter (fun v : Fin p.T => v.val < n.val ∧ (sourceCall v z.val).isSome) =
      insert s before := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, before]
    constructor
    · rintro ⟨hvn, hpresent⟩
      by_cases hvs : v.val < s.val
      · exact Or.inr ⟨hvs, hpresent⟩
      by_cases heq : v = s
      · exact Or.inl heq
      have hsv : s.val < v.val := by
        have hne : v.val ≠ s.val := fun h => heq (Fin.ext h)
        omega
      have hnone := (ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none
        rate rewards C_star C_h v z.val).mp (hcall v hsv hvn)
      rw [hnone] at hpresent
      cases hpresent
    · rintro (rfl | ⟨hvs, hpresent⟩)
      · exact ⟨hsn, z.property⟩
      · exact ⟨by omega, hpresent⟩
  have hnot : s ∉ before := by simp only [before, Finset.mem_filter,
    Finset.mem_univ, lt_self_iff_false, false_and, and_false, not_false_eq_true]
  change (Finset.univ.filter _).card = before.card + 1
  rw [hdates, Finset.card_insert_of_notMem hnot]

/-- Consecutive actual invocation dates advance the actual native rank by
one, regardless of the intervening disabled or collection dates. -/
theorem nativeRank_consecutive (s q : Fin p.T) (z : NativeSource s)
    (hsq : s.val < q.val) (hcall : CallFree s q.castSucc z.val) : rankAt q z.val = rankAt s z.val + 1 :=
  boundaryCallCount_native_interval rate rewards C_star C_h s q.castSucc z hsq hcall

/-- An ordinary noncall date advances the boundary without changing the
actual number of invocations. The successor may be the horizon. -/
theorem boundaryCallCount_noncall (q : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : noCallAt rate rewards C_star C_h q z) : boundaryCallCount rate rewards C_star C_h q.succ z =
      boundaryCallCount rate rewards C_star C_h q.castSucc z := by
  have hnone := (ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none
    rate rewards C_star C_h q z).mp hc
  apply congrArg Finset.card
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases heq : v = q
  · subst v
    simp only [hnone, Option.isSome_none, Bool.false_eq_true, and_false]
  · have hne : v.val ≠ q.val := fun h => heq (Fin.ext h)
    constructor
    · rintro ⟨hv, hp⟩
      exact ⟨by change v.val < q.val + 1 at hv; change v.val < q.val; omega, hp⟩
    · rintro ⟨hv, hp⟩
      exact ⟨by change v.val < q.val + 1; change v.val < q.val at hv; omega, hp⟩

/-- The first actual list occurrence has native rank zero. -/
theorem nativeRank_first (u t : Fin p.T) (theta : ReferenceFirstCollectionSamplerCall.Theta p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hfirst : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = some (u, (t, theta))) : rankAt t z = 0 := by
  apply ReferenceCollectionSamplerChronology.nthCollectionCall_priorCallCount rate rewards C_star C_h 0 z u t theta
  simpa only [ReferenceCollectionSamplerChronology.nthCollectionCall_zero] using hfirst

private theorem insertion_congr_of_prefix {X : Type*} (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (n : ℕ) (hn : n ≤ q.val) (f : BootstrapPrivateRoundStreams.SourceInput p → X)
    (hf : ∀ z, f z = f (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (vector : FullVector) : f (insertVector q z vector) = f z :=
  (hf _).trans ((congrArg f (ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent
    control0 q n hn z (ReferenceFirstCollectionRenewalVectorInsertion.ctrl q z vector))).trans (hf z).symm)

/-- Same-date insertion leaves every earlier and current pre-choice call
fixed, since those calls factor through the unchanged strict physical past. -/
theorem callAt_insert (control0 : TimeControls) (q v : Fin p.T) (hvq : v.val ≤ q.val) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (vector : FullVector) : sourceCall v (insertVector q z vector) = sourceCall v z := by
  exact insertion_congr_of_prefix control0 q v.val hvq _
    (ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 v) z vector

/-- Insertion changes no chronological rank already reached, including the
rank at the insertion date itself. -/
theorem nativeRank_insert (control0 : TimeControls) (q v : Fin p.T)
    (hvq : v.val ≤ q.val) (z : BootstrapPrivateRoundStreams.SourceInput p) (vector : FullVector) : rankAt v (insertVector q z vector) =
    rankAt v z := by
  exact insertion_congr_of_prefix control0 q v.val hvq _
    (ReferenceCollectionSamplerChronology.priorCallCount_factor rate rewards C_star C_h control0 v) z vector

/-- Complete generated PRE lists, for an arbitrary native seed/history, are
fixed by a same-date insertion. This does not identify a supplied list with
a generated list; it identifies the two literal calendar computations. -/
theorem noncallCalendar_insert (control0 : TimeControls) (s q : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a : AuxiliaryArray) (initial : SlowSet p × List Cell) (vector : FullVector) :
    noncallRun s (insertVector q z vector)
        a initial q.val = noncallRun s z a initial q.val := by
  exact insertion_congr_of_prefix control0 q q.val le_rfl _
    (fun z => ReferencePostInvocationPrefixLocality.noncallCalendar_sourcePrefix
      rate rewards C_star C_h control0 q.val q.isLt.le s z a initial q.val le_rfl) z vector

/-- All native numerical fields, at arbitrary rank, belong to the one
complete original calendar word, including its first overflow update. -/
theorem nativeCell_originalWord (control0 : TimeControls) (t : Fin p.T) (z : NativeSource t) (x : UniformScalar) :
    let W := originalWord z.val (nativeInvocation_launch rate rewards C_star C_h t z)
    let c := nativeCellAt control0 t z x
    c.time = t ∧ c.before = run Q (W.take (t.val - start z.val)) ∧
      c.after = run Q (W.take (t.val + 1 - start z.val)) ∧ ∃ hk : t.val - start z.val < W.length,
        c.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
          W[t.val - start z.val] ∧ c.arrivals = RecordedQueueRun.acceptedRecord Q c.before W[t.val - start z.val] ∧
        c.service = fun j => RecordedQueueRun.recordService (4 * (Q).n) (c.before.registers j) (c.arrivals j) := by
  dsimp only
  let W := originalWord z.val (nativeInvocation_launch rate rewards C_star C_h t z)
  let r := nativeRecordAt t z
  let c := nativeSourceAt t z
  have hspec := nativeSourceCell_spec rate rewards C_star C_h t z
  have hcell : cell0 rate r = some c.input := by
    change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).or _ = _
    rw [hspec.2.2, Option.some_or]
  obtain ⟨i, hi, hrecord, hst⟩ := actualRecord_index rate rewards C_star C_h t z.val r hspec.1
  have hlookup : (records z.val)[t.val - start z.val]? = some r := by
    rw [← hi, List.getElem?_eq_getElem i.isLt, hrecord]
  have hk : t.val - start z.val < W.length := by
    rw [actualOriginalWord_length]
    exact (List.getElem?_eq_some_iff.mp hlookup).1
  have hm := congrArg (fun L => L[t.val - start z.val]?) (originalWord_record_map rate rewards C_star C_h z.val
      (nativeInvocation_launch rate rewards C_star C_h t z))
  rw [List.getElem?_map, hlookup, Option.map_some, hcell,
    List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some] at hm
  have hc : c.input = W[t.val - start z.val] := Option.some.inj (Option.some.inj hm)
  have hb := nativeCell_before_word rate rewards C_star C_h control0 t z x
  refine ⟨nativeCell_time rate rewards C_star C_h control0 t z x, hb, ?_, hk, ?_, ?_, rfl⟩
  · change RecordedQueueRun.step Q (nativeBeforeAt control0 t z) c.input = _
    change nativeBeforeAt control0 t z = _ at hb
    rw [hb, hc, Nat.sub_add_comm hst, ← List.take_append_getElem hk, RecordedSlowRefresh.run_append_singleton]
  · change ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates c.input = _
    rw [hc]
  · change RecordedQueueRun.acceptedRecord Q _ c.input = _
    rw [hc]
    rfl

/-- The installed date is the actual payload birth time, at every rank. -/
theorem nativeInvocation_sigma (t : Fin p.T) (z : NativeSource t) :
    (nativeSourceAt t z).selected.view.payload.sigma = t := by
  obtain ⟨i, rb, _qb, _base, hr, _heq, _chosen, _next, hb, hp⟩ :=
    nativeInvocation_installation rate rewards C_star C_h t z
  apply Fin.ext
  rw [← hp]
  exact (ReferenceAssignmentPayloadChronology.installationBirth_time_eq _ _ hb).trans
    (congrArg Fin.val (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t _ _ hr).2.2.1)

section NativeRetainedWindow

open ReferenceActualCollectionHiddenRefreshPath
open ReferencePostInvocationRetainedEndpointRecurrence

variable (e n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p) (hz : z ∈ collectionPrefixCell rate rewards C_star C_h e n)

local notation "W" => collectionWord rate rewards C_star C_h e n z hz
local notation "P" => oldPayload rate rewards C_star C_h e n z hz

private theorem numericalCoordinates_injective : Function.Injective
    (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates (p := p)) := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  cases h
  rfl

private theorem clear_before (k : ℕ) (hk : k ≤ n) :
    (collectionState rate rewards C_star C_h e n z hz k).overflow = false := by
  exact prefix_clear_mono rate W k n hk (collectionWord_bound rate rewards C_star C_h e n z hz)
    (collectionWord_retained rate rewards C_star C_h e n z hz)

private theorem cutoff_not_later (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (h : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ReferenceCollectionPhaseHistory.laterChosen x = false := by
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at h
  unfold ReferenceCollectionPhaseHistory.laterChosen
  cases hc : (ReferenceActivePhysicalStep.prepare x).coordinator <;> simp only [hc] at h ⊢
  next r q base outcome => cases outcome <;> simp_all only

private theorem continuing_not_cutoff (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (h : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r = true) :
    ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
  have hp : (ReferenceActivePhysicalStep.prepare r.input).coordinator =
      r.output.preparation.coordinator := by rw [r.output_eq]; rfl
  unfold ReferenceCollectionPhaseHistory.cutoffChosen
  rw [hp]
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at h
  cases hc : r.output.preparation.coordinator <;> simp only [hc] at h ⊢
  next r q base outcome => cases outcome <;> simp_all only

include hz in
/-- A canonical retained window at a later PRE boundary starts strictly after
the actual produced installation. The trigger may be exactly the produced date. -/
theorem native_before_cutoff (t q : Fin p.T) (htq : t.val < q.val)
    (s : NativeSource t) (hs : s.val = z) (hdate : start z + n = q.val) : t.val < start z + e := by
  subst z
  obtain ⟨i, _rb, _qb, _base, hr, _heq, hlater, _⟩ := nativeInvocation_installation rate rewards C_star C_h t s
  have htime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate s.val rewards C_star C_h i.val _ (List.getElem?_eq_getElem i.isLt)
  have htimeI := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t s.val _ hr).2.2.1
  obtain ⟨he, r, owned, base, hlive, hcut, _⟩ := collectionPrefixCell_live rate rewards C_star C_h e n s.val hz
  have hno : ∀ k : Fin (records s.val).length, e < k.val → k.val < n →
      ReferenceCollectionPhaseHistory.laterChosen (records s.val)[k.val].input = false := by
    obtain ⟨_, _, _, hc⟩ := hz
    rw [hlive] at hc
    exact hc.2.2.1
  rcases lt_trichotomy e i.val with hlt | heq | hlt
  · have hn := hno i hlt (by omega)
    rw [hlater] at hn
    cases hn
  · have hn := cutoff_not_later rate (records s.val)[e].input hcut
    have ht : ReferenceCollectionPhaseHistory.laterChosen (records s.val)[e].input = true := by
      simpa only [← heq] using hlater
    rw [ht] at hn
    cases hn
  · omega

private theorem cutoff_record : sourceRecord (cutoffDate rate rewards C_star C_h e n z hz) z =
      some ((records z)[e]'(collectionPrefixCell_live rate rewards C_star C_h e n z hz).choose) := by
  have he := (collectionPrefixCell_live rate rewards C_star C_h e n z hz).choose
  change (if start z ≤ start z + e then (records z)[start z + e - start z]? else none) = _
  rw [ite_eq_left (by omega), Nat.add_sub_cancel_left, List.getElem?_eq_getElem he]

/-- The canonical old payload is the one installed by the produced invocation. -/
theorem oldPayload_eq_native (t q : Fin p.T) (htq : t.val < q.val)
    (s : NativeSource t) (hs : s.val = z) (hdate : start z + n = q.val)
    (hcall : NoCallBetween rate rewards C_star C_h t q.castSucc z) :
    P = (nativeSourceAt t s).selected.view.payload := by
  subst z
  have hafter := native_before_cutoff rate rewards C_star C_h e n s.val hz t q htq s rfl hdate
  obtain ⟨he, r, owned, base, hlive, _hcut, _hboundary, hp⟩ :=
    collectionPrefixCell_live rate rewards C_star C_h e n s.val hz
  let v := cutoffDate rate rewards C_star C_h e n s.val hz
  have hv := cutoff_record rate rewards C_star C_h e n s.val hz
  have hret := (nativeInvocation_retained_interval rate rewards C_star C_h t q.castSucc s
    hcall).1 v hafter (by change start s.val + e ≤ q.val; have := hz.1; omega) _ hv
  rw [hlive, ReferenceAssignmentPayloadPersistence.storedPayload_live] at hret
  exact (oldPayload_eq rate rewards C_star C_h e n s.val hz r.payload hp).trans (Option.some.inj hret)


include hz in
private theorem window_collection_domain (t q : Fin p.T) (htq : t.val < q.val)
    (s : NativeSource t) (hs : s.val = z) (hdate : start z + n = q.val)
    (hcall : NoCallBetween rate rewards C_star C_h t q.castSucc z) (k : ℕ) (hk : e + k < n) :
    z ∈ collectionDomain ⟨start z + e + k, by omega⟩ := by
  have hafter := native_before_cutoff rate rewards C_star C_h e n z hz t q htq s hs hdate
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
      have hc : z ∈ collectionDomain v := ih (by omega)
      have hv := (collectionRecord_spec rate rewards C_star C_h v ⟨z, hc⟩).1
      obtain ⟨ledger, saved, hout⟩ := collectionRecord_output rate rewards C_star C_h v ⟨z, hc⟩
      have hnocall := hcall v' (by dsimp only [v']; omega) (by change start z + e + (k + 1) < q.val; omega)
      rcases noncall_phase_coverage rate rewards C_star C_h v' z (by dsimp only [v']; omega)
        hnocall with hl | hc'
      · obtain ⟨r, owned, base, started, hin, _⟩ := continuingRecord_frame rate rewards C_star C_h v' ⟨z, hl⟩
        have hv' := (continuingSourceCell_spec rate rewards C_star C_h v' ⟨z, hl⟩).1
        have hadj := congrArg ReferenceActivePhysicalStep.State.coordinator
          (actualRecord_adjacent rate rewards C_star C_h v v' (by dsimp only [v, v']; omega)
            z _ _ hv hv')
        rw [hin, hout] at hadj
        cases hadj
      · exact hc'

private theorem native_trigger_next (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (S : RecordedQueueRun.RunState p.K) (a : AuxiliaryArray) (hclear : S.overflow = false)
    (hbit : FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time = true) :
    (appendLogicalCell r c S a).nextSlowSet = DeferredRefreshUniformKernels.sampleResidual p Q S c.input
        c.selected.view.payload.anchor c.selected.view.payload.anchor_pos (a (r.input.time, 1)) := by
  simp only [appendLogicalCell, hclear, hbit, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ite_false, ite_true]
  rfl

private theorem trigger_initialization (control0 : TimeControls) (b : Bool) (t q : Fin p.T)
    (htq : t.val < q.val) (s : NativeSource t) (hs : s.val = z) (hdate : start z + n = q.val)
    (hcall : NoCallBetween rate rewards C_star C_h t q.castSucc z)
    (a : AuxiliaryArray) (H : List Cell) : (noncallRun t z a
      ((nativeCellAt control0 t s (a (t, if b then 0 else 1))).nextSlowSet, H)
      (start z + e)).map Prod.fst = some (triggerSampler rate rewards C_star C_h e n z hz (evaluatorArray b t a
          (actualCoordinateIndex rate rewards C_star C_h e n z hz (n - e) le_rfl (.inl ())))) := by
  have hepos := collectionPrefixCell_trigger_positive rate rewards C_star C_h e n z hz
  have heb := hz.1
  have hafter := native_before_cutoff rate rewards C_star C_h e n z hz t q htq s hs hdate
  have hP := oldPayload_eq_native rate rewards C_star C_h e n z hz t q htq s hs hdate hcall
  let v : Fin p.T := ⟨start z + e - 1, by have := q.isLt; omega⟩
  let d := cutoffDate rate rewards C_star C_h e n z hz
  have hvd : v.val + 1 = d.val := by dsimp only [v, d, cutoffDate]; omega
  have htv : t.val ≤ v.val := by dsimp only [v]; omega
  have hstart : start z ≤ t.val := by
    have hr := (nativeSourceCell_spec rate rewards C_star C_h t s).1
    have hd := (actualRecord_index rate rewards C_star C_h t s.val _ hr).choose_spec.2.2
    simpa only [hs] using hd
  have hvq : v.val < q.val := by dsimp only [v]; omega
  have hi : v.val - start z = e - 1 := by dsimp only [v]; omega
  have haddr : actualCoordinateIndex rate rewards C_star C_h e n z hz (n - e) le_rfl (.inl ()) = (v, 1) := by
    apply Prod.ext
    · exact Fin.ext (actualCoordinateIndex_trigger rate rewards C_star C_h e n z hz _ _).1
    · exact (actualCoordinateIndex_trigger rate rewards C_star C_h e n z hz _ _).2
  rw [haddr]
  obtain ⟨stamp, hstamp, hproposal⟩ := collectionPrefixCell_trigger_proposal rate rewards C_star C_h e n z hz
  have hstampEq : stamp = v := Fin.ext (by change stamp.val + 1 = start z + e at hstamp; dsimp only [v]; omega)
  rw [hstampEq] at hproposal
  have hbit (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate) (hr : sourceRecord v z = some r) :
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time = true := by
    have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h v z r hr
    change FollowerCutoffScan.completeRowProposalBit p rate.eta.val (r.input.rows r.input.selected) r.input.time = true
    rw [hf.1, hf.2.1, hf.2.2.1]
    exact hproposal
  let initial := ((nativeCellAt control0 t s (a (t, if b then 0 else 1))).nextSlowSet, H)
  have hfree : NoCallBetween rate rewards C_star C_h t d.castSucc z := by
    intro r htr hrd
    exact hcall r htr (by change r.val < q.val; change r.val < start z + e at hrd; omega)
  have hsome := (noncallCalendar_isSome rate rewards C_star C_h t d.castSucc z a initial).mpr hfree
  obtain ⟨state, hstate⟩ := Option.isSome_iff_exists.mp hsome
  change noncallRun t z a initial (start z + e) = some state at hstate
  rw [hstate, Option.map_some]
  congr 1
  by_cases heq : v = t
  · have hinit := noncallCalendar_initial rate rewards C_star C_h t z a initial (start z + e)
      (by have hv := congrArg Fin.val heq; dsimp only [v] at hv; omega)
    have hstateEq := Option.some.inj (hstate.symm.trans hinit)
    rw [hstateEq]
    change (nativeCellAt control0 t s (a (t, if b then 0 else 1))).nextSlowSet = _
    have hidx : t.val - start z = e - 1 := by rw [← heq]; exact hi
    have hn := nativeCell_originalWord rate rewards C_star C_h control0 t s (a (t, if b then 0 else 1))
    have hbefore : nativeBeforeAt control0 t s = collectionState rate rewards C_star C_h e n z hz (e - 1) := by
      simpa only [nativeCell, appendLogicalCell, collectionState, collectionWord, hs, hidx] using hn.2.1
    obtain ⟨hbound, hnum, _⟩ := hn.2.2.2
    have hinput : (nativeSourceAt t s).input = triggerInput rate rewards C_star C_h e n z hz := by
      apply numericalCoordinates_injective
      simpa only [nativeCell, appendLogicalCell, triggerInput, collectionWord, hs, hidx,
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates] using hnum
    have hclear : (nativeBeforeAt control0 t s).overflow = false := by
      rw [hbefore]
      exact clear_before rate rewards C_star C_h e n z hz (e - 1) (by omega)
    have hr : sourceRecord v z = some (nativeRecordAt t s) := by
      simpa only [heq, hs] using (nativeSourceCell_spec rate rewards C_star C_h t s).1
    rw [nativeCell, native_trigger_next rate _ _ _ _ hclear (hbit _ hr)]
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
    have hstate' : noncallRun t z a initial (v.val + 1) = some state := by
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
    have hpay := nativeInvocation_continuingPayload rate rewards C_star C_h t v s hlt hcallS
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

private theorem generated_window_recurrence (control0 : TimeControls) (b : Bool) (t q : Fin p.T)
    (htq : t.val < q.val) (s : NativeSource t) (hs : s.val = z) (hdate : start z + n = q.val)
    (hcall : NoCallBetween rate rewards C_star C_h t q.castSucc z)
    (a : AuxiliaryArray) (H : List Cell) : (noncallRun t z a
      ((nativeCellAt control0 t s (a (t, if b then 0 else 1))).nextSlowSet, H)
      q.val).map Prod.fst = some (sampledArrayPath rate rewards C_star C_h e n z hz (n - e) le_rfl
        (evaluatorArray b t a) (Fin.last (n - e))) := by
  let initial := ((nativeCellAt control0 t s (a (t, if b then 0 else 1))).nextSlowSet, H)
  let D := sampledArrayPath rate rewards C_star C_h e n z hz (n - e) le_rfl (evaluatorArray b t a)
  have hafter := native_before_cutoff rate rewards C_star C_h e n z hz t q htq s hs hdate
  have heb := hz.1
  have hP := oldPayload_eq_native rate rewards C_star C_h e n z hz t q htq s hs hdate hcall
  have hinit := trigger_initialization rate rewards C_star C_h e n z hz control0 b t q htq s hs hdate hcall a H
  have hzero : ∃ state, noncallRun t z a initial (start z + e) = some state ∧ state.1 = D 0 := by
    cases hr : noncallRun t z a initial (start z + e) with
    | none => rw [hr, Option.map_none] at hinit; cases hinit
    | some state =>
        rw [hr, Option.map_some] at hinit
        exact ⟨state, rfl, Option.some.inj hinit⟩
  have hrec : ∀ k (hk : k ≤ n - e), ∃ state, noncallRun t z a initial (start z + e + k) = some state ∧
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
        have hcol : z ∈ collectionDomain v :=
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
        have hcolS : s.val ∈ collectionDomain v := by simpa only [hs] using hcol
        have hpayS := nativeInvocation_collectionPayload rate rewards C_star C_h t v s htv hcallS hcolS
        have hpay : (collectionArguments rate rewards C_star C_h v ⟨z, hcol⟩).1 = P := by
          have hx : (⟨s.val, hcolS⟩ : CollectionDateSource rate rewards C_star C_h v) = ⟨z, hcol⟩ := Subtype.ext hs
          exact (congrArg (fun x : CollectionDateSource rate rewards C_star C_h v =>
            (collectionArguments rate rewards C_star C_h v x).1) hx).symm.trans (hpayS.trans hP.symm)
        have hclear : (collectionBefore rate rewards C_star C_h v ⟨z, hcol⟩).overflow = false := by
          rw [hbefore]
          exact clear_before rate rewards C_star C_h e n z hz (e + k) (by omega)
        have hstep := appendNoncallDate_collection_refresh rate rewards C_star C_h z v hcol a state hclear
        rw [hbefore, hinput, hpay, hseed] at hstep
        have hD : D ⟨k + 1, by omega⟩ = DeferredRefreshUniformKernels.sampleRecordedRefresh p Q
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
        rw [hindex, noncallCalendar, hrun, Option.bind_some, dite_eq_left ⟨htv, v.isLt⟩, ite_eq_left hnocall]
  obtain ⟨state, hrun, hseed⟩ := hrec (n - e) le_rfl
  have hindex : start z + e + (n - e) = q.val := by omega
  rw [hindex] at hrun
  rw [hrun, Option.map_some]
  exact congrArg some hseed

/-- Deterministic retained endpoint on an arbitrary native-origin segment.
The actual nonrenewed selector and PRE-clear numerical word produce the
sampler parameter, old payload, trigger bound, and the original-array path.
No endpoint law, mixture, generated-history correctness, or rank is assumed.
This pointwise theorem does not supply independence of its consumed block. -/
theorem native_retained_endpoint (control0 : TimeControls) (b : Bool) (t q : Fin p.T)
    (htq : t.val < q.val) (s : NativeSource t) (a : AuxiliaryArray) (L : List Cell)
    (hbetween : CallFree t q.castSucc s.val)
    (hcall : ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall
      rate rewards C_star C_h q s.val)
    (hclear : ∃ o, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h q.val s.val = some o ∧ o.2.1 = false) :
    ∃ (e n : ℕ) (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
      (hw : s.val ∈ collectionPrefixCell rate rewards C_star C_h e n), sourceCall q s.val =
        some (cutoff, theta) ∧ start s.val + n = q.val ∧
      theta.1 = (RecordedCorrectedWindow.actualPrefixSamplerMass p Q
        (ReferenceActualCollectionNonrenewedEndpointFibreJoin.collectionQueue_sourceCap rate)
        (collectionWord rate rewards C_star C_h e n s.val hw) e n
        (collectionPrefixCell_trigger_positive rate rewards C_star C_h e n s.val hw)
        hw.1 (collectionWord_bound rate rewards C_star C_h e n s.val hw)).weight ∧
      theta.2 = (oldPayload rate rewards C_star C_h e n s.val hw).anchor ∧
      oldPayload rate rewards C_star C_h e n s.val hw = (nativeSourceAt t s).selected.view.payload ∧
      numericalAt q.castSucc s.val = some (collectionState rate rewards C_star C_h e n s.val hw n) ∧
      t.val ≤ start s.val + e - 1 ∧ (noncallRun t s.val a
        ((nativeCellAt control0 t s (a (t, if b then 0 else 1))).nextSlowSet,
          L ++ [nativeCellAt control0 t s (a (t, if b then 0 else 1))])
        q.val).map Prod.fst = some (sampledArrayPath rate rewards C_star C_h e n s.val hw (n - e) le_rfl
          (evaluatorArray b t a) (Fin.last (n - e))) ∧
      Function.Injective (consumedAddress rate rewards C_star C_h e n s.val hw b t (n - e) le_rfl) ∧
      ∀ i, let j := consumedAddress rate rewards C_star C_h e n s.val hw b t (n - e) le_rfl i
        t.val < j.1.val ∨ (j.1 = t ∧ j.2 = if b then 0 else 1) := by
  obtain ⟨e, n, record, cutoff, theta, hw, _hr, hcallAt, hdate, hweight, hanchor⟩ :=
    ReferenceActualCollectionNonrenewedEndpointFibreJoin.actualNonrenewedCollectionCall_parameters
      rate rewards C_star C_h q s.val hcall hclear
  have hafter := native_before_cutoff rate rewards C_star C_h e n s.val hw t q htq s rfl hdate
  have htrigger : t.val ≤ start s.val + e - 1 := by omega
  have hpay := oldPayload_eq_native rate rewards C_star C_h e n s.val hw t q htq s rfl hdate hbetween
  have hword := prefixNumerical_actualWord rate rewards C_star C_h q.castSucc s.val
    (collectionPrefixCell_launch rate rewards C_star C_h e n s.val hw) (by change start s.val ≤ q.val; omega)
  have hidx : q.val - start s.val = n := by omega
  have hnum : numericalAt q.castSucc s.val = some (collectionState rate rewards C_star C_h e n s.val hw n) := by
    simpa only [Fin.val_castSucc, collectionState, collectionWord, hidx] using hword
  refine ⟨e, n, cutoff, theta, hw, hcallAt, hdate, hweight, hanchor, hpay, hnum, htrigger, ?_,
    consumedAddress_injective rate rewards C_star C_h e n s.val hw b t (n - e) le_rfl,
    consumedAddress_unused rate rewards C_star C_h e n s.val hw b t htrigger (n - e) le_rfl⟩
  exact generated_window_recurrence rate rewards C_star C_h e n s.val hw
    control0 b t q htq s rfl hdate hbetween a _

end NativeRetainedWindow

end Bandits.Support.ReferenceGeneratedNativeInvocationGeometry
