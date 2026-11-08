/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeHistoryTransport
public import Bandits.Support.ReferenceGeneratedCalendarQuantizedRoundKernel
public import Bandits.Support.ReferenceGeneratedCalendarEpisodeInitialLaw

/-!
# Retained FAST parameters, readouts, and ROOT component identity

Sources: ZIP4 `04_slow_fast_learner.tex:16-37,96-114,140-215,323-390`
and `06_interruptions.tex:391-426`.

This component exports retained FAST parameters/readouts, local marginals, and
the actual generated ROOT identity. Source witnesses are produced internally;
local branch, clear-PRE, and source predicates remain explicit in helpers.
The ROOT identity uses the actual installed anchor/PRE on a clear current cell.
The episode-start retained history-PMF identity and full FAST/channel law
remain open; no law of the incoming slow set is stipulated.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationGeneratedAlignment
open ReferenceGeneratedInvocationCallSplice
open ReferenceActualCollectionHiddenRefreshPath (actualOriginalWord actualOriginalWord_length
  actualOriginalWord_numericalPrefix)
open ReferenceCompletePhysicalHistory (physicalStart completeSuffixRecords completeSuffixRecords_length)
open ReferenceFirstLaunchNumericalCell (queueParameters)
open ReferenceCorrectedInitializationLaunch (correctedLaunch)
open ReferenceFirstCollectionLogicalNumericalAlignment (originalWord_calendar_prefix)
open RecordedQueueRun (run scoreWeight)
open ReferenceSourcePrefixHistoryFiltration (actualRecord)
open ReferenceCompleteLaterLiveComplementPrefixReplay (continuingTest continuingPrefix)
open ReferenceFirstCorrectedNextCalendarWordJoin (calendarReplay rawCalendar)
open CanonicalFastSampling (FastArm)

namespace Bandits.Support.ReferenceGeneratedCalendarRetainedFastCore

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "Q" => queueParameters rate
local notation "start " z:max => physicalStart rate z rewards C_star C_h
local notation "records " z:max => completeSuffixRecords rate z rewards C_star C_h
local notation "NativeSource" => InvocationSource rate rewards C_star C_h
local notation "liveCell" => continuingSourceCell rate rewards C_star C_h
local notation "liveRecord" => continuingRecord rate rewards C_star C_h
local notation "livePRE" => continuingBefore rate rewards C_star C_h
local notation "liveDomain" => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h
local notation "CallFree" => NoCallBetween rate rewards C_star C_h
local notation "sourceRecord" => actualRecord rate rewards C_star C_h
local notation "originalWord" => actualOriginalWord rate rewards C_star C_h

/-- Every intervening noncall before a continuing-LIVE query is continuing LIVE. -/
theorem nativeInvocation_live_interval (t q : Fin p.T) (z : NativeSource t) (hcall : CallFree t q.castSucc z.val)
    (hlive : z.val ∈ liveDomain q) :
    ∀ v : Fin p.T, t.val < v.val → v.val ≤ q.val → z.val ∈ liveDomain v := by
  have hst := (actualRecord_index rate rewards C_star C_h t z.val _
    (nativeSourceCell_spec rate rewards C_star C_h t z).1).choose_spec.2.2
  have h : ∀ k : ℕ, ∀ v : Fin p.T, v.val + k = q.val → t.val < v.val → z.val ∈ liveDomain v := by
    intro k
    induction k with
    | zero =>
        intro v hv _htv
        have heq : v = q := Fin.ext (by omega)
        subst v
        exact hlive
    | succ k ih =>
        intro v hv htv
        let next : Fin p.T := ⟨v.val + 1, by omega⟩
        have hnext := ih next (by dsimp only [next]; omega) (by dsimp only [next]; omega)
        exact continuing_previous_domain rate rewards C_star C_h v next rfl ⟨z.val, hnext⟩
          (by change start z.val < v.val; omega)
          (hcall v htv (by change v.val < q.val; omega))
  intro v htv hvq
  exact h (q.val - v.val) v (by omega) htv

/-- The LIVE query belongs to this installation's maximal continuing prefix. -/
theorem nativeInvocation_live_prefix_index (t q : Fin p.T) (z : NativeSource t) (htq : t.val < q.val)
    (hcall : CallFree t q.castSucc z.val) (hlive : z.val ∈ liveDomain q) :
    q.val - start z.val < t.val + 1 - start z.val + (continuingPrefix
        rate rewards C_star C_h z.val (t.val + 1 - start z.val)).length := by
  let R := records z.val
  let k := t.val + 1 - start z.val
  let L := R.drop k
  let n := q.val - start z.val - k + 1
  have hst := (actualRecord_index rate rewards C_star C_h t z.val _
    (nativeSourceCell_spec rate rewards C_star C_h t z).1).choose_spec.2.2
  have hRlen : R.length = p.T - start z.val := completeSuffixRecords_length rate z.val rewards C_star C_h
  have hn : n ≤ L.length := by
    dsimp only [n, L, k]
    rw [List.length_drop, hRlen]
    omega
  have htest : ∀ r ∈ L.take n, continuingTest r = true := by
    intro r hr
    obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hr
    have hin : i < n := hi.trans_le (List.length_take_le n L)
    have hiL : i < L.length := by omega
    have hiR : k + i < R.length := by dsimp only [L] at hiL; rw [List.length_drop] at hiL; omega
    have hrecord : R[k + i] = r := by
      simpa only [List.getElem_take, L, List.getElem_drop] using hir
    let v : Fin p.T := ⟨start z.val + (k + i), by rw [hRlen] at hiR; omega⟩
    have htv : t.val < v.val := by dsimp only [v, k]; omega
    have hvq : v.val ≤ q.val := by dsimp only [v, n, k] at *; omega
    have hvLive := nativeInvocation_live_interval rate rewards C_star C_h t q z hcall hlive v htv hvq
    have hlookup : sourceRecord v z.val = some r := by
      rw [actualRecord, ite_eq_left (by dsimp only [v]; omega : start z.val ≤ v.val)]
      change R[(start z.val + (k + i)) - start z.val]? = some r
      rw [Nat.add_sub_cancel_left, List.getElem?_eq_getElem hiR, hrecord]
    have heq : r = liveRecord v ⟨z.val, hvLive⟩ :=
      Option.some.inj (hlookup.symm.trans (continuingSourceCell_spec rate rewards C_star C_h v ⟨z.val, hvLive⟩).1)
    rw [heq]
    exact (continuingRecord_frame rate rewards C_star C_h v ⟨z.val, hvLive⟩).choose_spec.choose_spec.choose_spec.choose_spec.2.1
  have htake : L.takeWhile continuingTest = L.take n ++ (L.drop n).takeWhile continuingTest := by
    conv_lhs => rw [← List.take_append_drop n L]
    exact List.takeWhile_append_of_pos htest
  have hlen := congrArg List.length htake
  rw [List.length_append, List.length_take, Nat.min_eq_left hn] at hlen
  change q.val - start z.val < k + (L.takeWhile continuingTest).length
  dsimp only [n, k] at hlen ⊢
  omega

private theorem originalWord_weight_of_clear (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hl : ∃ active, correctedLaunch rate z rewards C_star C_h = some active)
    (n : ℕ) (hn : n ≤ (originalWord z hl).length) (hc : (run Q ((originalWord z hl).take n)).overflow = false) :
    scoreWeight Q (run Q ((originalWord z hl).take n)) =
      (fun j => AssignmentScoreReconstruction.sourceWeightBase p ^
        (calendarReplay rate (originalWord z hl) j n).1) := by
  have hpre : n ≤ UnstoppedRecordedQueueComparison.firstOverflowPrefix Q (originalWord z hl) := by
    by_contra hnot
    have hf := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
      Q (originalWord z hl) n hn).mpr (by omega)
    rw [hc] at hf
    cases hf
  have hw := (actualOriginalWord_numericalPrefix rate rewards C_star C_h z hl n hn).2.1
  simpa only [Nat.min_eq_left hpre] using hw

/-- At a clear LIVE PRE state the physical complement equals the all-arm numerical restriction. -/
theorem nativeInvocation_live_complement (t q : Fin p.T) (z : NativeSource t) (htq : t.val < q.val)
    (hcall : CallFree t q.castSucc z.val) (hlive : z.val ∈ liveDomain q)
    (hclear : (livePRE q ⟨z.val, hlive⟩).overflow = false) :
    ∀ j : FastArm (liveCell q ⟨z.val, hlive⟩).selected.view.payload.slowSet,
      (liveCell q ⟨z.val, hlive⟩).selected.view.complementWeights j =
        scoreWeight Q (livePRE q ⟨z.val, hlive⟩) j.val := by
  let R := records z.val
  let r := liveRecord q ⟨z.val, hlive⟩
  let W := continuingNumericalWord rate rewards C_star C_h q ⟨z.val, hlive⟩
  let h := q.val - start z.val
  obtain ⟨b, _rb0, _qb0, _beta0, hr0, _heq0, hb, _hnext0, _hbirth0, _hpay0⟩ :=
    ReferenceGeneratedNativeInvocationGeometry.nativeInvocation_installation rate rewards C_star C_h t z
  obtain ⟨bi, hbiindex, hbirec, hst⟩ := actualRecord_index rate rewards C_star C_h t z.val _ hr0
  have hbieq : bi = b := by
    apply Fin.ext
    have he := congrArg (fun r : Record rate => r.input.time.val) hbirec
    have ht := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z.val b
    have hti := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z.val bi
    omega
  have hbindex : b.val = t.val - start z.val := by simpa only [hbieq] using hbiindex
  obtain ⟨iq, hiq, hqrec, _hsq⟩ := actualRecord_index rate rewards C_star C_h q z.val r
    (continuingSourceCell_spec rate rewards C_star C_h q ⟨z.val, hlive⟩).1
  have hhR : h < R.length := by dsimp only [h]; rw [← hiq]; exact iq.isLt
  have hWlen : W.length = R.length := actualOriginalWord_length rate rewards C_star C_h z.val _
  obtain ⟨P0, rb, qb, beta, cell, _native, hP0len, _hP0map, _hP0prefix, _hinit,
      _hnext, _hbirth, _hstrict, _hbase, _hcell, _hninput, _hnpayload, _henabled,
      _hbirthPrefix, _hbirthSlots, hseed, _hdown, hbranch⟩ :=
    ReferenceCompleteInstallationOutsideCalendarReplay.actual_later_installation_complement_calendar_replay
      rate rewards C_star C_h z.val b hb
  rcases hbranch with hterminal | ⟨k, C, hk, _hstate, _hClen, _hCmap, _hCtimes,
    heR, _heT, _hHlen, hprefix, _hslots, _hdisabled, hcounts, htail⟩
  · omega
  clear htail
  have hkvalue : k.val = t.val + 1 - start z.val :=
    hk.trans ((congrArg (fun n => n + 1) hbindex).trans (Nat.sub_add_comm hst).symm)
  have hqin := nativeInvocation_live_prefix_index rate rewards C_star C_h t q z htq hcall hlive
  rw [← hkvalue] at hqin
  let count := h - k.val
  have hkh : k.val ≤ h := by dsimp only [h]; omega
  have hcount : count ≤ (continuingPrefix
      rate rewards C_star C_h z.val k.val).length := by dsimp only [count, h]; omega
  have hsum : k.val + count = h := by dsimp only [count]; omega
  obtain ⟨rn, qn, hpn, _houtn, hinn, hnum⟩ := hcounts count hcount
  have hrecord : R[k.val + count] = r := by simpa only [hsum, hiq] using hqrec
  have hinoption := hinn (by change k.val + count < R.length; omega)
  rw [List.getElem?_eq_getElem (by change k.val + count < R.length; omega), Option.map_some, hrecord] at hinoption
  have hinrn : r.input.state.coordinator = .live rn qn beta := Option.some.inj hinoption
  let H := P0 ++ [cell] ++ C
  have hprefixH := hprefix h hkh (by dsimp only [h]; omega)
  have hcalendar := (originalWord_calendar_prefix rate rewards C_star C_h z.val
    (continuing_launch rate rewards C_star C_h q ⟨z.val, hlive⟩) q.castSucc (by change start z.val ≤ q.val; omega)).2.2
  have hdate : start z.val + h = q.val := by
    dsimp only [h]
    omega
  rw [hdate] at hprefixH
  have htake : H.take h = W.take h := Option.some.inj (hprefixH.symm.trans hcalendar)
  have hbirthLength : (P0 ++ [cell]).length = k.val := by
    rw [List.length_append, List.length_singleton, hP0len]
    exact hk.symm
  have htakeH : H.take h = (P0 ++ [cell]) ++ C.take count := by
    change ((P0 ++ [cell]) ++ C).take h = _
    rw [List.take_append, List.take_of_length_le (by omega : (P0 ++ [cell]).length ≤ h), hbirthLength]
  have hreplay (j : FastArm rb.payload.slowSet) :
      QueueReplay.replay (4 * rate.n) (rb.complementScores j, qb.queue j) (rawCalendar rate j.val (C.take count)) =
      calendarReplay rate W j.val h := by
    rw [(hseed j).1]
    unfold calendarReplay
    rw [List.take_length, ← QueueReplay.replay_append, ← htake, htakeH]
    simp only [rawCalendar, List.map_append]
  have hregisters (j : FastArm rn.payload.slowSet) :
      rn.complementScores j = (calendarReplay rate W j.val h).1 := by
    let j0 : FastArm rb.payload.slowSet := ⟨j.val, by simpa only [← hpn] using j.property⟩
    obtain ⟨j1, hj1, hvalue, _hservice⟩ := hnum j0
    have hjeq : j1 = j := Subtype.ext hj1
    subst j1
    exact (congrArg Prod.fst hvalue).trans (congrArg Prod.fst (hreplay j0))
  have hweight := originalWord_weight_of_clear rate rewards C_star C_h z.val
    (continuing_launch rate rewards C_star C_h q ⟨z.val, hlive⟩) h
    (by change h ≤ W.length; omega) hclear
  change scoreWeight Q (run Q (W.take h)) =
    (fun j => AssignmentScoreReconstruction.sourceWeightBase p ^ (calendarReplay rate W j h).1) at hweight
  obtain ⟨regs, owned, base, started, hin, _htest, _hpayload, _hstart, _hframe, hview⟩ :=
    continuingRecord_frame rate rewards C_star C_h q ⟨z.val, hlive⟩
  change r.input.state.coordinator = .live regs owned base at hin
  have hregs : regs = rn := Option.some.inj (congrArg (fun configuration => match configuration with
      | .live registers _ _ => some registers
      | _ => none) (hin.symm.trans hinrn))
  subst regs
  let property := fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
    ∀ j : FastArm view.payload.slowSet, view.complementWeights j = scoreWeight Q (livePRE q ⟨z.val, hlive⟩) j.val
  apply Eq.mpr (congrArg property hview)
  intro j
  change rn.complementWeights j = scoreWeight Q (run Q (W.take h)) j.val
  rw [hweight]
  change AssignmentScoreReconstruction.sourceWeightBase p ^ rn.complementScores j = _
  rw [hregisters j]



open ReferenceGeneratedCalendarEpisodeSlowLaw
open ReferenceGeneratedCalendarEpisodeHistoryTransport
open ReferenceOriginalCalendarEpisodeChronology

local instance sourceMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := Subtype.instMeasurableSpace

attribute [local instance] ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.sumMeasurableSingleton
  ReferenceRankInstallationRecorderFoundation.optionSingleton

variable (control0 : ContinuousLearningRows.TimeControl p)

local notation "Omega" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h
local notation "Z" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0

local instance selectedTerminalLaw_finite (ids : Option (CompletePublicTable.IDArray p)) :
    IsFiniteMeasure (ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)) := by
  cases ids <;> dsimp only [Option.elim_none, Option.elim_some] <;> infer_instance

/-- The actual start and incoming-clear event. No POST condition is imposed. -/
def retainedDomain (s q : Fin p.T) : Set Omega :=
  episodeStartEvent rate rewards C_star C_h control0 s ∩
    retainedEvent rate rewards C_star C_h control0 s q

theorem measurableSet_retainedDomain (s q : Fin p.T) :
    MeasurableSet (retainedDomain rate rewards C_star C_h control0 s q) :=
  ((measurableSet_sourceStartEvent rate rewards C_star C_h control0 s).preimage
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource rate rewards C_star C_h control0)).inter
    (measurableSet_retainedEvent rate rewards C_star C_h control0 s q)

omit rewards C_star C_h control0 in
/-- The existing categorical FAST PMF evaluated at two actual numerical states.
Its definition needs positivity only and is literal on its entire carrier. -/
def numericalFastPMF (A S : RecordedQueueRun.RunState p.K) (U : SlowSet p) : PMF (FastArm U) :=
  ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate (scoreWeight Q A) (scoreWeight Q S)
    (RecordedSlowRefresh.scoreWeight_pos Q A) (RecordedSlowRefresh.scoreWeight_pos Q S) U

omit rewards C_star C_h control0 in
theorem numericalFastPMF_eq_qGamma (A S : RecordedQueueRun.RunState p.K)
    (hlo : ∀ i, scoreWeight Q A i ≤ scoreWeight Q S i)
    (hhi : ∀ i, scoreWeight Q S i ≤ 2 * scoreWeight Q A i) (U : SlowSet p) :
    numericalFastPMF rate A S U = CanonicalFastSampling.qGammaPMF p rate.eta.val
      rate.eta.property rate.sourceCap (scoreWeight Q A) (scoreWeight Q S)
      (RecordedSlowRefresh.scoreWeight_pos Q A) (RecordedSlowRefresh.scoreWeight_pos Q S)
      hlo hhi U := by
  ext j
  rw [numericalFastPMF, ReferencePostInvocationCollectionNativeLaw.collectionFastPMF_apply,
    CanonicalFastSampling.qGammaPMF_apply,
    collectionFastMass_eq_qGamma rate _ _ _ _ hlo hhi]

/-- Simultaneous actual source witnesses and the all-arm envelope, under either
original terminal law. The old set's distribution is left unrestricted. -/
theorem ae_retained_fast_parameters (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q : Fin p.T),
      w ∈ retainedDomain rate rewards C_star C_h control0 s q →
      ∃ (e : LogicalCell p rate) (rho : Fin (records (Z w)).length)
        (P : ReferenceActivePhysicalStep.Payload rate) (A : RecordedQueueRun.RunState p.K),
        currentMark rate rewards C_star C_h control0 q w = some e ∧ e.time = q ∧
        (records (Z w))[rho.val].input.time = s ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth (records (Z w))[rho.val] P ∧
        prefixNumerical rate rewards C_star C_h s.castSucc
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w).1.1 = some A ∧
        A.overflow = false ∧ P.anchor = scoreWeight Q A ∧
        sourceEpisodeReplay rate rewards C_star C_h s q
          (sourceEstimateHistory rate rewards C_star C_h control0 s q w) = some e.before ∧
        e.before.overflow = false ∧ e.numerical.1 = true ∧
        ∀ i, scoreWeight Q A i ≤ scoreWeight Q e.before i ∧
          scoreWeight Q e.before i < 2 * scoreWeight Q A i := by
  filter_upwards [ae_sourceEpisodeMass_actual rate rewards C_star C_h control0 ids,
    ae_sourceEpisodeReplay rate rewards C_star C_h control0 ids,
    ae_source_estimate_numerical_update rate rewards C_star C_h control0 ids] with w hm hr hu
  intro s q hE
  obtain ⟨hs, hret⟩ := hE
  obtain ⟨hsq, hq, hclear⟩ := hret
  obtain ⟨e, rho, P, A, he, ht, hb, hA, hAc, hanchor, _hmass⟩ := hm s q hs ⟨hsq, hq, hclear⟩
  obtain ⟨hen, hpre, _hpost, _harrival, _hupdate, _hservice⟩ := hu q e he
  have hec : e.before.overflow = false := by
    simpa only [hpre, Option.any_some, Bool.not_eq_true'] using hclear
  have hrep := (hr s q hs hsq hq).trans hpre
  have het := ((currentMark_eq_some_iff rate rewards C_star C_h control0 q w e).mp he).2
  refine ⟨e, rho, P, A, he, het, ht, hb, hA, hAc, hanchor, hrep, hec, hen, ?_⟩
  let z := Z w
  let hl := complete_record_launch rate rewards C_star C_h z rho
  let W := actualOriginalWord rate rewards C_star C_h z hl
  have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z rho
  have hstarts : start z ≤ s.val := by rw [ht] at htime; omega
  have hAfull : prefixNumerical rate rewards C_star C_h s.castSucc z = some A := by
    rw [ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix
      rate rewards C_star C_h control0 s.castSucc s.val le_rfl z]
    exact hA
  have hAword : A = run Q (W.take (s.val - start z)) :=
    Option.some.inj (hAfull.symm.trans
      (prefixNumerical_actualWord rate rewards C_star C_h s.castSucc z hl hstarts))
  have hSword : e.before = run Q (W.take (q.val - start z)) :=
    Option.some.inj (hpre.symm.trans
      (prefixNumerical_actualWord rate rewards C_star C_h q.castSucc z hl (hstarts.trans hsq)))
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hH : 0 < H := FollowerCutoffScan.episodeHorizon_pos_of_source_cap
    p rate.eta.val rate.eta.property rate.sourceCap
  have hgap := (RecordedEpisodeStability.sourceEpisodeEnd_bounds p.T H (s.val + 1) hH
    (by omega) (by have := s.isLt; omega)).2.2
  have hspan : q.val - s.val ≤ H := by
    change min (p.T + 1) (H * ((s.val + 1) / H + 1)) - (s.val + 1) ≤ H at hgap
    change q.val + 1 < min (p.T + 1) (H * ((s.val + 1) / H + 1)) at hq
    omega
  have hstartOrder : s.val - start z ≤ q.val - start z := Nat.sub_le_sub_right hsq _
  have hlen : ((W.drop (s.val - start z)).take
      ((q.val - start z) - (s.val - start z))).length ≤
      ReplayWeightStability.episodeHorizon (Q).eta := by
    apply (List.length_take_le _ _).trans
    change (q.val - start z) - (s.val - start z) ≤ H
    omega
  have hfactor := RecordedEpisodeStability.run_take_eq_execute_drop Q W
    (s.val - start z) (q.val - start z) hstartOrder
  intro i
  obtain ⟨hlo, hhi, _hlog, _heta⟩ := RecordedEpisodeStability.execute_source_weight_envelope Q
    (run Q (W.take (s.val - start z))) _ i hlen
  rw [← hfactor, ← hAword, ← hSword] at hlo hhi
  exact ⟨hlo, hhi⟩


omit control0 in
/-- Integrate only FAST, retaining the exact accepted history and incoming U.
Absent seed or replay observations supply zero, without a default state. -/
def historyFastTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞)
    (h : History rate s q) (U : SlowSet p) : ℝ≥0∞ :=
  match prefixNumerical rate rewards C_star C_h s.castSucc h.1.1,
      sourceEpisodeReplay rate rewards C_star C_h s q h with
  | some A, some S => ∑ j : FastArm U, Phi (h, (U, j.val)) * numericalFastPMF rate A S U j
  | _, _ => 0

omit control0 in
theorem measurable_historyFastTest (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    Measurable (fun hU : History rate s q × SlowSet p =>
      historyFastTest rate rewards C_star C_h s q Phi hU.1 hU.2) := by
  let f : History rate s q ×
      (Option (RecordedQueueRun.RunState p.K) × Option (RecordedQueueRun.RunState p.K) × SlowSet p) → ℝ≥0∞ :=
    fun v => match v.2.1, v.2.2.1 with
      | some A, some S => ∑ j : FastArm v.2.2.2,
          Phi (v.1, (v.2.2.2, j.val)) * numericalFastPMF rate A S v.2.2.2 j
      | _, _ => 0
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    rintro ⟨a, b, U⟩
    cases a with
    | none => exact measurable_const
    | some A =>
      cases b with
      | none => exact measurable_const
      | some S =>
        change Measurable (fun h : History rate s q => ∑ j : FastArm U,
          Phi (h, (U, j.val)) * numericalFastPMF rate A S U j)
        exact Finset.measurable_sum Finset.univ (fun j _ =>
          (hPhi.comp (measurable_id.prodMk (measurable_const.prodMk measurable_const))).mul measurable_const)
  exact hf.comp (measurable_fst.prodMk
    (((ReferencePostInvocationPrefixLocality.measurable_prefixNumerical rate rewards C_star C_h s.castSucc).comp
      measurable_fst.fst.fst).prodMk
      (((measurable_sourceEpisodeReplay rate rewards C_star C_h s q).comp measurable_fst).prodMk measurable_snd)))

omit control0 in
/-- Literal finite mean reward under the existing FAST PMF. -/
def numericalFastReward (q : Fin p.T) (A S : RecordedQueueRun.RunState p.K) (U : SlowSet p) : ℝ :=
  ∑ j : FastArm U, (numericalFastPMF rate A S U j).toReal *
    ((∑ i ∈ U.val, ((rewards q i).val : ℝ) / (D p : ℝ)) +
      ((rewards q j.val).val : ℝ) / (D p : ℝ))

omit C_star C_h control0 in
theorem numericalFastReward_eq_integral (q : Fin p.T) (A S : RecordedQueueRun.RunState p.K)
    (U : SlowSet p) :
    numericalFastReward rate rewards q A S U =
      ∫ j : FastArm U, MixedAuxiliaryReward.oneRoundAuxiliaryReward
        (fun i => ((rewards q i).val : ℝ) / (D p : ℝ)) U j
        ∂(numericalFastPMF rate A S U).toMeasure := by
  rw [PMF.integral_eq_sum]
  rfl

omit C_star C_h control0 in
theorem numericalFastReward_bounds (q : Fin p.T) (A S : RecordedQueueRun.RunState p.K)
    (U : SlowSet p) :
    0 ≤ numericalFastReward rate rewards q A S U ∧ numericalFastReward rate rewards q A S U ≤ p.m := by
  let r : Fin p.K → ℝ := fun i => ((rewards q i).val : ℝ) / (D p : ℝ)
  have hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1 := fun i =>
    ReferenceGeneratedCalendarQuantizedRoundKernel.gridReward_mem rewards q i
  have hsum : ∑ j : FastArm U, (numericalFastPMF rate A S U j).toReal = 1 := by
    have hp : ∑ j : FastArm U, numericalFastPMF rate A S U j = 1 := by
      simpa only [tsum_fintype] using (numericalFastPMF rate A S U).tsum_coe
    rw [← ENNReal.toReal_sum (fun j _ => (numericalFastPMF rate A S U).apply_ne_top j),
      hp, ENNReal.toReal_one]
  change 0 ≤ ∑ j : FastArm U, (numericalFastPMF rate A S U j).toReal *
      MixedAuxiliaryReward.oneRoundAuxiliaryReward r U j ∧ _
  constructor
  · exact Finset.sum_nonneg fun j _ => mul_nonneg ENNReal.toReal_nonneg
      (MixedAuxiliaryReward.oneRoundAuxiliaryReward_bounds r hr U j).1
  · calc
      numericalFastReward rate rewards q A S U ≤
          ∑ j : FastArm U, (numericalFastPMF rate A S U j).toReal * (p.m : ℝ) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (MixedAuxiliaryReward.oneRoundAuxiliaryReward_bounds r hr U j).2 ENNReal.toReal_nonneg
      _ = p.m := by rw [← Finset.sum_mul, hsum, one_mul]

omit C_star C_h control0 in
/-- Reuse the accepted continuous/finite FAST reward conversion. -/
theorem numericalFastReward_eq_continuous (q : Fin p.T) (A S : RecordedQueueRun.RunState p.K)
    (hlo : ∀ i, scoreWeight Q A i ≤ scoreWeight Q S i)
    (hhi : ∀ i, scoreWeight Q S i ≤ 2 * scoreWeight Q A i) (U : SlowSet p) :
    numericalFastReward rate rewards q A S U =
      ∫ x : ContinuousCategorical.Scalar, MixedAuxiliaryReward.oneRoundAuxiliaryReward
        (fun i => ((rewards q i).val : ℝ) / (D p : ℝ)) U
        (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
          (scoreWeight Q A) (scoreWeight Q S) (RecordedSlowRefresh.scoreWeight_pos Q A)
          (RecordedSlowRefresh.scoreWeight_pos Q S) hlo hhi U x)
        ∂ContinuousCategorical.uniform := by
  rw [numericalFastReward_eq_integral, numericalFastPMF_eq_qGamma rate A S hlo hhi,
    FastRewardSliceLaw.qGammaPMF_integral_oneRoundAuxiliaryReward,
    FastRewardSliceLaw.integral_oneRoundAuxiliaryReward_sampleFast]

omit control0 in
/-- Reward mean at existing optional observations; no replacement state is used. -/
def historyFastReward (s q : Fin p.T) (h : History rate s q) (U : SlowSet p) : ℝ :=
  match prefixNumerical rate rewards C_star C_h s.castSucc h.1.1,
      sourceEpisodeReplay rate rewards C_star C_h s q h with
  | some A, some S => numericalFastReward rate rewards q A S U
  | _, _ => 0

omit control0 in
theorem measurable_historyFastReward (s q : Fin p.T) :
    Measurable (fun hU : History rate s q × SlowSet p =>
      historyFastReward rate rewards C_star C_h s q hU.1 hU.2) := by
  let f : Option (RecordedQueueRun.RunState p.K) ×
      (Option (RecordedQueueRun.RunState p.K) × SlowSet p) → ℝ := fun v =>
    match v.1, v.2.1 with
    | some A, some S => numericalFastReward rate rewards q A S v.2.2
    | _, _ => 0
  exact (measurable_of_countable f).comp
    (((ReferencePostInvocationPrefixLocality.measurable_prefixNumerical rate rewards C_star C_h s.castSucc).comp
      measurable_fst.fst.fst).prodMk
      (((measurable_sourceEpisodeReplay rate rewards C_star C_h s q).comp measurable_fst).prodMk measurable_snd))

omit control0 in
theorem historyFastReward_bounds (s q : Fin p.T) (h : History rate s q) (U : SlowSet p) :
    0 ≤ historyFastReward rate rewards C_star C_h s q h U ∧
      historyFastReward rate rewards C_star C_h s q h U ≤ p.m := by
  unfold historyFastReward
  split
  · exact numericalFastReward_bounds rate rewards q _ _ U
  · exact ⟨le_rfl, Nat.cast_nonneg _⟩

open ReferenceFirstLiveChronologicalPrefixMeasurability in
omit C_star C_h control0 in
theorem measurable_cellReward : Measurable (ReferenceInitialStoppedCalendar.cellReward rate rewards) := by
  let f : Fin p.T × (SlowSet p × Fin p.K) → ℝ := fun v =>
    (∑ i ∈ v.2.1.val, ((rewards v.1 i).val : ℝ) / (D p : ℝ)) +
      ((rewards v.1 v.2.2).val : ℝ) / (D p : ℝ)
  have ht : Measurable (fun e : LogicalCell p rate => e.time) := measurable_logicalCell_time
  have hU : Measurable (fun e : LogicalCell p rate => e.slowSet) :=
    measurable_logicalCell_slowSet.mono le_rfl le_top
  have hj : Measurable (fun e : LogicalCell p rate => e.fastArm) := measurable_logicalCell_fastArm
  have hf : Measurable f := measurable_of_finite f
  have hm : Measurable (fun e : LogicalCell p rate => f (e.time, (e.slowSet, e.fastArm))) :=
    hf.comp (ht.prodMk (hU.prodMk hj))
  change Measurable (fun e : LogicalCell p rate => f (e.time, (e.slowSet, e.fastArm)))
  exact hm


omit control0 in
/-- Take only the second marginal of the correlated continuing-LIVE pair.
The actual prepared snapshot and validity come from the source cell. -/
theorem continuing_pair_fast_marginal (q : Fin p.T)
    (z : ContinuingLiveSource rate rewards C_star C_h q) :
    let cell := continuingSourceCell rate rewards C_star C_h q z
    let v := cell.selected.view
    let valid := ReferenceLaterLiveNumericalReadout.selection_choiceValid cell.selected
    (ReferencePostInvocationLiveNativeLaw.nativePairLaw rate rewards C_star C_h q z).map Prod.snd =
      (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
        v.payload.anchor (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid)
        v.payload.slowSet).toMeasure.map (fun j => j.val) := by
  dsimp only
  let cell := continuingSourceCell rate rewards C_star C_h q z
  let v := cell.selected.view
  let valid := ReferenceLaterLiveNumericalReadout.selection_choiceValid cell.selected
  let U := SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment
  let mu := ReferencePostInvocationLiveNativeLaw.liveNativePairLaw rate
    (continuingRecord rate rewards C_star C_h q z) cell.selected cell.states
  have hslow : U = v.payload.slowSet := by
    apply Subtype.ext
    exact v.payload.assignment_image
  have hm := FastRewardSliceLaw.liveRecordingFastPushforward_snd p rate.eta.val
    rate.eta.property rate.sourceCap v.payload.anchor
    (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
    v.payload.anchor_pos
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid)
    v.payload.assignment (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)
  change mu.map Prod.snd = _ at hm
  calc
    _ = (mu.map Prod.snd).map (fun j : FastArm U => j.val) := by
      have herase : Measurable (fun y : Option (Fin p.K) × FastArm U => (y.1, y.2.val)) :=
        measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
      change (mu.map (fun y : Option (Fin p.K) × FastArm U => (y.1, y.2.val))).map Prod.snd = _
      rw [Measure.map_map measurable_snd herase,
        Measure.map_map measurable_subtype_coe measurable_snd]
      rfl
    _ = _ := by
      rw [hm]
      change ((CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
        v.payload.anchor (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid) U).toMeasure.map
        (fun j => j.val)) = _
      rw [hslow]

omit rewards C_star C_h control0 in
private theorem choiceFastPMF_eq_collection (t : Fin p.T)
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t v.complementWeights)
    (S : RecordedQueueRun.RunState p.K)
    (heq : ∀ j : FastArm v.payload.slowSet, v.complementWeights j = scoreWeight Q S j.val) :
    CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
      v.payload.anchor (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
      v.payload.anchor_pos (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid) v.payload.slowSet =
    ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate v.payload.anchor
      (scoreWeight Q S) v.payload.anchor_pos (RecordedSlowRefresh.scoreWeight_pos Q S) v.payload.slowSet := by
  have hw : (fun j : FastArm v.payload.slowSet =>
      ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights j.val) =
      fun j => scoreWeight Q S j.val := by
    funext j
    change (if h : j.val ∈ v.payload.slowSet.val then _ else _) = _
    rw [dite_eq_right (Finset.mem_sdiff.mp j.property).2]
    exact heq j
  ext j
  rw [CanonicalFastSampling.qGammaPMF_apply, ← collectionFastMass_eq_qGamma rate _ _ _
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid),
    ReferencePostInvocationCollectionNativeLaw.collectionFastPMF_apply]
  unfold collectionFastMass FastComplementLocality.localConditionalFastMass
    FastComplementLocality.localFastCandidateMass FastComplementLocality.localFastNormalizer
  rw [hw]

omit control0 in
/-- At any native rank, numerical complement weights give the actual LIVE
FAST marginal. Current weights on the slow arms are never identified. -/
theorem nativeInvocation_live_fast_marginal (t q : Fin p.T) (z : NativeSource t)
    (htq : t.val < q.val) (hcall : CallFree t q.castSucc z.val)
    (hlive : z.val ∈ liveDomain q) (hclear : (livePRE q ⟨z.val, hlive⟩).overflow = false) :
    let v := (liveCell q ⟨z.val, hlive⟩).selected.view
    (ReferencePostInvocationLiveNativeLaw.nativePairLaw rate rewards C_star C_h q ⟨z.val, hlive⟩).map Prod.snd =
      (ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate v.payload.anchor
        (scoreWeight Q (livePRE q ⟨z.val, hlive⟩)) v.payload.anchor_pos
        (RecordedSlowRefresh.scoreWeight_pos Q _) v.payload.slowSet).toMeasure.map (fun j => j.val) := by
  dsimp only
  let cell := liveCell q ⟨z.val, hlive⟩
  let v := cell.selected.view
  let valid := ReferenceLaterLiveNumericalReadout.selection_choiceValid cell.selected
  have hcomp := nativeInvocation_live_complement rate rewards C_star C_h t q z htq hcall hlive hclear
  have hpmf := choiceFastPMF_eq_collection rate (liveRecord q ⟨z.val, hlive⟩).input.time v valid (livePRE q ⟨z.val, hlive⟩) hcomp
  exact (continuing_pair_fast_marginal rate rewards C_star C_h q ⟨z.val, hlive⟩).trans
    (congrArg (fun pmf : PMF (FastArm v.payload.slowSet) => pmf.toMeasure.map (fun j => j.val)) hpmf)


/-- Literal actual reward multiplier. An absent actual mark contributes zero. -/
def actualRewardTest (s q : Fin p.T) (g : History rate s q × SlowSet p → ℝ) (w : Omega) : ℝ :=
  match currentMark rate rewards C_star C_h control0 q w with
  | none => 0
  | some e => g (sourceEstimateHistory rate rewards C_star C_h control0 s q w, e.slowSet) *
      ReferenceInitialStoppedCalendar.cellReward rate rewards e

/-- The FAST mean uses the same actual incoming slow set and accepted history. -/
def meanRewardTest (s q : Fin p.T) (g : History rate s q × SlowSet p → ℝ) (w : Omega) : ℝ :=
  match currentMark rate rewards C_star C_h control0 q w with
  | none => 0
  | some e => g (sourceEstimateHistory rate rewards C_star C_h control0 s q w, e.slowSet) *
      historyFastReward rate rewards C_star C_h s q
        (sourceEstimateHistory rate rewards C_star C_h control0 s q w) e.slowSet

private theorem measurable_optional_history {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Zero Y]
    (f : LogicalCell p rate × X → Y) (hf : Measurable f) :
    Measurable (fun v : Option (LogicalCell p rate) × X =>
      match v.1 with | none => 0 | some e => f (e, v.2)) := by
  have h := (hf.sumElim (measurable_const : Measurable (fun _ : PUnit × X => (0 : Y)))).comp
    (MeasurableEquiv.sumProdDistrib (LogicalCell p rate) PUnit X).measurable_toFun
  have hpair := h.comp (((comap_measurable (Equiv.optionEquivSumPUnit (LogicalCell p rate))).comp
    measurable_fst).prodMk measurable_snd)
  convert hpair using 1
  funext v
  rcases v with ⟨e, x⟩
  cases e <;> rfl

omit rewards C_star C_h control0 in
private theorem measurable_clearFast_test (s q : Fin p.T)
    (Phi : History rate s q × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    Measurable (fun eh : Option (LogicalCell p rate) × History rate s q =>
      eh.1.elim 0 (fun e => if e.before.overflow = false then Phi (eh.2, (e.slowSet, e.fastArm)) else 0)) := by
  let f : LogicalCell p rate × History rate s q → ℝ≥0∞ := fun eh =>
    if eh.1.before.overflow = false then Phi (eh.2, (eh.1.slowSet, eh.1.fastArm)) else 0
  have hU : Measurable (fun e : LogicalCell p rate => e.slowSet) :=
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_slowSet.mono le_rfl le_top
  have hf : Measurable f := (hPhi.comp (measurable_snd.prodMk ((hU.comp measurable_fst).prodMk
    (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_fastArm.comp measurable_fst)))).ite
      (((measurable_of_countable (fun S : RecordedQueueRun.RunState p.K => S.overflow)).comp
        (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_before.comp measurable_fst))
        (measurableSet_singleton false)) measurable_const
  convert measurable_optional_history rate f hf using 1
  funext eh
  rcases eh with ⟨e, h⟩
  cases e <;> rfl

open ReferenceFirstLiveChronologicalPrefixMeasurability in
theorem measurable_actualRewardTest (s q : Fin p.T) (g : History rate s q × SlowSet p → ℝ)
    (hg : Measurable g) : Measurable (actualRewardTest rate rewards C_star C_h control0 s q g) := by
  let f : Option (LogicalCell p rate) × History rate s q → ℝ := fun v =>
    match v.1 with
    | none => 0
    | some e => g (v.2, e.slowSet) * ReferenceInitialStoppedCalendar.cellReward rate rewards e
  have hf : Measurable f := by
    apply measurable_optional_history rate (fun v : LogicalCell p rate × History rate s q =>
      g (v.2, v.1.slowSet) * ReferenceInitialStoppedCalendar.cellReward rate rewards v.1)
    have hU : Measurable (fun e : LogicalCell p rate => e.slowSet) :=
      measurable_logicalCell_slowSet.mono le_rfl le_top
    exact (hg.comp (measurable_snd.prodMk (hU.comp measurable_fst))).mul
      ((measurable_cellReward rate rewards).comp measurable_fst)
  exact hf.comp ((measurable_currentMark rate rewards C_star C_h control0 q).prodMk
    (measurable_sourceEstimateHistory rate rewards C_star C_h control0 s q))

open ReferenceFirstLiveChronologicalPrefixMeasurability in
theorem measurable_meanRewardTest (s q : Fin p.T) (g : History rate s q × SlowSet p → ℝ)
    (hg : Measurable g) : Measurable (meanRewardTest rate rewards C_star C_h control0 s q g) := by
  let f : Option (LogicalCell p rate) × History rate s q → ℝ := fun v =>
    match v.1 with
    | none => 0
    | some e => g (v.2, e.slowSet) * historyFastReward rate rewards C_star C_h s q v.2 e.slowSet
  have hf : Measurable f := by
    apply measurable_optional_history rate (fun v : LogicalCell p rate × History rate s q =>
      g (v.2, v.1.slowSet) * historyFastReward rate rewards C_star C_h s q v.2 v.1.slowSet)
    have hU : Measurable (fun e : LogicalCell p rate => e.slowSet) :=
      measurable_logicalCell_slowSet.mono le_rfl le_top
    exact (hg.mul (measurable_historyFastReward rate rewards C_star C_h s q)).comp
      (measurable_snd.prodMk (hU.comp measurable_fst))
  exact hf.comp ((measurable_currentMark rate rewards C_star C_h control0 q).prodMk
    (measurable_sourceEstimateHistory rate rewards C_star C_h control0 s q))

theorem actualRewardTest_norm_le (s q : Fin p.T) (g : History rate s q × SlowSet p → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, ‖g v‖ ≤ C) (w : Omega) :
    ‖actualRewardTest rate rewards C_star C_h control0 s q g w‖ ≤ C * p.m := by
  unfold actualRewardTest
  split
  · simpa only [norm_zero] using mul_nonneg hC (Nat.cast_nonneg p.m)
  · next e he =>
      have hb := ReferenceExhaustiveGeneratedCalendarSourceLaw.cellReward_bounds rate rewards e
      rw [norm_mul, Real.norm_of_nonneg hb.1]
      exact mul_le_mul (hbound _) hb.2 hb.1 hC

theorem meanRewardTest_norm_le (s q : Fin p.T) (g : History rate s q × SlowSet p → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, ‖g v‖ ≤ C) (w : Omega) :
    ‖meanRewardTest rate rewards C_star C_h control0 s q g w‖ ≤ C * p.m := by
  unfold meanRewardTest
  split
  · simpa only [norm_zero] using mul_nonneg hC (Nat.cast_nonneg p.m)
  · next e he =>
      have hb := historyFastReward_bounds rate rewards C_star C_h s q
        (sourceEstimateHistory rate rewards C_star C_h control0 s q w) e.slowSet
      rw [norm_mul, Real.norm_of_nonneg hb.1]
      exact mul_le_mul (hbound _) hb.2 hb.1 hC

theorem integrable_actualRewardTest (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (g : History rate s q × SlowSet p → ℝ) (hg : Measurable g)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, ‖g v‖ ≤ C) :
    IntegrableOn (actualRewardTest rate rewards C_star C_h control0 s q g)
      (retainedDomain rate rewards C_star C_h control0 s q)
      (ids.elim
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)) := by
  apply Integrable.of_bound (measurable_actualRewardTest rate rewards C_star C_h control0 s q g hg).aestronglyMeasurable
    (C * p.m)
  exact Filter.Eventually.of_forall (actualRewardTest_norm_le rate rewards C_star C_h control0 s q g C hC hbound)

theorem integrable_meanRewardTest (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (g : History rate s q × SlowSet p → ℝ) (hg : Measurable g)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, ‖g v‖ ≤ C) :
    IntegrableOn (meanRewardTest rate rewards C_star C_h control0 s q g)
      (retainedDomain rate rewards C_star C_h control0 s q)
      (ids.elim
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)) := by
  apply Integrable.of_bound (measurable_meanRewardTest rate rewards C_star C_h control0 s q g hg).aestronglyMeasurable
    (C * p.m)
  exact Filter.Eventually.of_forall (meanRewardTest_norm_le rate rewards C_star C_h control0 s q g C hC hbound)


/-- Actual continuing-LIVE cell test at every installation rank. The original
whole control and both auxiliary labels are integrated out; recorder, proposal
and refresh dependence disappear through the genuine FAST marginal only. -/
theorem nativeInvocation_live_fast_test (t q : Fin p.T) (z : NativeSource t)
    (htq : t.val < q.val) (hcall : CallFree t q.castSucc z.val)
    (hlive : z.val ∈ liveDomain q) (hclear : (livePRE q ⟨z.val, hlive⟩).overflow = false)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (f : SlowSet p × Fin p.K → ℝ≥0∞) :
    let zz : ContinuingLiveSource rate rewards C_star C_h q := ⟨z.val, hlive⟩
    let v := (liveCell q zz).selected.view
    (∫⁻ y : ContinuousLearningRows.TimeControl p × (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar),
      let e := continuingLogicalCell rate rewards C_star C_h q
        (ReferencePostInvocationLiveNativeLaw.sourceAt rate rewards C_star C_h control0 q zz y.1)
        (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a y.2)
      f (e.slowSet, e.fastArm)
      ∂(ContinuousLearningRows.timeControlLaw p).prod
        (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)) =
      ∑ j : FastArm v.payload.slowSet, f (v.payload.slowSet, j.val) *
        ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate v.payload.anchor
          (scoreWeight Q (livePRE q zz)) v.payload.anchor_pos
          (RecordedSlowRefresh.scoreWeight_pos Q _) v.payload.slowSet j := by
  dsimp only
  let zz : ContinuingLiveSource rate rewards C_star C_h q := ⟨z.val, hlive⟩
  let v := (liveCell q zz).selected.view
  let pair := ReferencePostInvocationLiveNativeLaw.physicalPair rate rewards C_star C_h q zz
  let test : Fin p.K → ℝ≥0∞ := fun j => f (v.payload.slowSet, j)
  have hp := ReferencePostInvocationLiveNativeLaw.physicalPair_law rate rewards C_star C_h q zz
  have ht : Measurable test := measurable_of_finite _
  have htest : Measurable (fun c => test (pair c).2) := ht.comp (measurable_snd.comp hp.1)
  have he (y : ContinuousLearningRows.TimeControl p ×
      (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar)) :
      f ((continuingLogicalCell rate rewards C_star C_h q
        (ReferencePostInvocationLiveNativeLaw.sourceAt rate rewards C_star C_h control0 q zz y.1)
        (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a y.2)).slowSet,
        (continuingLogicalCell rate rewards C_star C_h q
          (ReferencePostInvocationLiveNativeLaw.sourceAt rate rewards C_star C_h control0 q zz y.1)
          (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a y.2)).fastArm) =
        test (pair y.1).2 := by
    rw [ReferencePostInvocationLiveNativeLaw.sourceAt_logicalCell]
    simp only [ReferencePostInvocationLiveNativeLaw.controlledCell, hclear, Bool.false_eq_true,
      ite_false, test, pair, v, zz]
  trans ∫⁻ y : ContinuousLearningRows.TimeControl p ×
      (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar), test (pair y.1).2
      ∂(ContinuousLearningRows.timeControlLaw p).prod
        (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)
  · exact lintegral_congr he
  rw [lintegral_prod (fun y : ContinuousLearningRows.TimeControl p ×
    (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar) => test (pair y.1).2)
    (htest.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  have hmap : (ContinuousLearningRows.timeControlLaw p).map (fun c => (pair c).2) =
      (ReferencePostInvocationLiveNativeLaw.nativePairLaw rate rewards C_star C_h q zz).map Prod.snd := by
    rw [← hp.2, Measure.map_map measurable_snd hp.1]
    rfl
  calc
    _ = ∫⁻ j, test j ∂(ContinuousLearningRows.timeControlLaw p).map (fun c => (pair c).2) :=
      (lintegral_map ht (measurable_snd.comp hp.1)).symm
    _ = ∫⁻ j, test j ∂(ReferencePostInvocationLiveNativeLaw.nativePairLaw rate rewards C_star C_h q zz).map Prod.snd :=
      congrArg (fun mu => ∫⁻ j, test j ∂mu) hmap
    _ = _ := by
      rw [nativeInvocation_live_fast_marginal rate rewards C_star C_h t q z htq hcall hlive hclear,
        lintegral_map ht measurable_subtype_coe, lintegral_fintype]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j)]


/-- At a retained actual mark the operative physical choice has the SAME
installed episode anchor as the history seed. The source's enabled record,
selection and episode origin are all produced, with no supplied coverage. -/
theorem ae_retained_selected_anchor (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (s q : Fin p.T), w ∈ retainedDomain rate rewards C_star C_h control0 s q →
        ∃ (e : LogicalCell p rate) (A : RecordedQueueRun.RunState p.K)
          (r : Record rate) (c : RecordedQueueRun.RoundInput p.K)
          (v : ReferenceActivePhysicalStep.Selection r.input),
          currentMark rate rewards C_star C_h control0 q w = some e ∧
          prefixNumerical rate rewards C_star C_h s.castSucc
            (sourceEstimateHistory rate rewards C_star C_h control0 s q w).1.1 = some A ∧
          sourceEpisodeReplay rate rewards C_star C_h s q
            (sourceEstimateHistory rate rewards C_star C_h control0 s q w) = some e.before ∧
          sourceRecord q (Z w) = some r ∧
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧ c.enabled = true ∧
          r.output.preparation.coordinator.selection = some v ∧
          v.view.payload.anchor = scoreWeight Q A ∧
          (∀ i, c.rate i = CanonicalRecordingRates.xi p rate.eta.val (scoreWeight Q A) i) ∧
          ∀ i, scoreWeight Q A i ≤ scoreWeight Q e.before i ∧
            scoreWeight Q e.before i < 2 * scoreWeight Q A i := by
  filter_upwards [ae_retained_fast_parameters rate rewards C_star C_h control0 ids] with w hw
  intro s q hE
  obtain ⟨hs, hret⟩ := hE
  obtain ⟨hsq, hq, hclear⟩ := hret
  obtain ⟨e, _rho, _P, A, he, _het, _ht, _hb, hA, _hAc, _hanchor, hS, _hSc, _hen, henv⟩ :=
    hw s q ⟨hs, hsq, hq, hclear⟩
  have hen : ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled
      rate rewards C_star C_h q (Z w) = true :=
    (currentMark_isSome_iff rate rewards C_star C_h control0 q w).mp (by rw [he]; rfl)
  obtain ⟨rho, P, r, c, v, hr, hc, hcen, hcover, huniq, hb, _hPuniq, _hbefore,
    hv, hanchor, hrates, _hgrid, _hclock⟩ :=
    nominalEnabled_episode_data rate rewards C_star C_h (Z w) q hen
  obtain ⟨rho0, ht0, hbirth0⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s (Z w) hs
  have hcover0 : EpisodeCovers (records (Z w))[rho0.val] q := ⟨hbirth0, ht0 ▸ hsq, ht0 ▸ hq⟩
  have hrho : rho0 = rho := huniq rho0 hcover0
  have ht : (records (Z w))[rho.val].input.time = s := by simpa only [hrho] using ht0
  obtain ⟨A0, hA0, _hA0c, hPanchor⟩ := episode_anchor_of_cover
    rate rewards C_star C_h control0 (Z w) q rho P hcover hb hclear
  rw [ht] at hA0
  have hAA : A0 = A := Option.some.inj (hA0.symm.trans hA)
  subst A0
  refine ⟨e, A, r, c, v, he, hA, hS, hr, hc, hcen, hv, hanchor.trans hPanchor, ?_, henv⟩
  intro i
  rw [hrates i, hPanchor]


section GeneratedLive

open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarJointRebase
open ReferenceGeneratedCalendarRoundInnovation
open ReferenceGeneratedCalendarNoncallRoundLaw

variable (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "stored" => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0
local notation "past" => calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0

/-- The accepted source estimate history ignores the complete current
innovation on a generated PRE boundary. No alternative history is constructed. -/
theorem calendarSourceHistory_fillInnovation (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k)
    (w : Sample k) (x : ReferencePostInvocationSupportedDisintegration.Innovation p) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le
      (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
        (by change t0.val < t0.val + 1 + k; omega) k (w, x)) =
      calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le w := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let hafter : t0.val < q.val := by dsimp only [q]; omega
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q hafter k
  have hp := calendarRoundPast_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 q hafter
    k hk.le le_rfl (w, x)
  have hsource := congrArg (fun v : BootstrapPrivateRoundStreams.SourceInput p ×
      (SlowSet p × List (LogicalCell p rate)) => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val v.1) hp
  change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val (current k hk.le (fill (w, x)))) =
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val (current k hk.le w)) at hsource
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 s.val q.val hs,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 s.val q.val hs] at hsource
  have hlist := congrArg (fun v : BootstrapPrivateRoundStreams.SourceInput p ×
      (SlowSet p × List (LogicalCell p rate)) => v.2.2) hp
  change (stored k hk.le (fill (w, x))).2 = (stored k hk.le w).2 at hlist
  unfold calendarSourceHistory
  apply Prod.ext
  · exact Prod.ext hsource (congrArg (fun L : List (LogicalCell p rate) =>
      L.filter (fun e => e.time.val < s.val)) hlist)
  · funext v
    exact congrArg (fun L : List (LogicalCell p rate) =>
      sourceOptionalEstimate rate (L.find? (fun e => e.time == v.val))) hlist

/-- The generated LIVE refill law with arbitrary tests of EXACTLY the accepted
source estimate history, the actual incoming set and FAST. This is a local
branch law; the exhaustive terminal component sum is not asserted here. -/
theorem calendar_live_fast_refill_test (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k) (w : Sample k)
    (hlive : current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩)
    (hclear : (continuingBefore rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
      ⟨current k hk.le w, hlive⟩).overflow = false)
    (Phi : History rate s ⟨t0.val + 1 + k, hk⟩ × (SlowSet p × Fin p.K) → ℝ≥0∞) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
      (by change t0.val < t0.val + 1 + k; omega) k
    let H := calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le w
    let zz : ContinuingLiveSource rate rewards C_star C_h q := ⟨current k hk.le w, hlive⟩
    let view := (continuingSourceCell rate rewards C_star C_h q zz).selected.view
    (∫⁻ x, match calendarNoncallCell rate rewards C_star C_h control0 b0 u0 t0 k hk (fill (w, x)) with
      | none => 0
      | some e => Phi (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le
          (fill (w, x)), (e.slowSet, e.fastArm)) ∂ReferencePostInvocationSupportedDisintegration.innovationLaw (p := p)) =
      ∑ j : FastArm view.payload.slowSet, Phi (H, (view.payload.slowSet, j.val)) *
        ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate view.payload.anchor
          (scoreWeight Q (continuingBefore rate rewards C_star C_h q zz)) view.payload.anchor_pos
          (RecordedSlowRefresh.scoreWeight_pos Q _) view.payload.slowSet j := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o := observe k hk.le w
  let z := calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  have horigin := calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  have h := nativeInvocation_live_fast_test rate rewards C_star C_h control0 o.1 q z horigin.1
    horigin.2.2 hlive hclear (original k w).1.2
    (fun v => Phi (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le w, v))
  refine Eq.trans ?_ h
  apply lintegral_congr
  intro x
  rw [calendarNoncallCell_fill_live rate rewards C_star C_h control0 b0 u0 t0 k hk w hlive x,
    calendarSourceHistory_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 s k hk hs w x,
    ReferencePostInvocationLiveNativeLaw.sourceAt_logicalCell]
  rfl


/-- The actual CALL kernel's second marginal, with its whole assignment vector
retained, uses the actual numerical PRE. Recorder and FAST are not factored. -/
theorem calendar_call_fast_marginal (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (vector : AssignmentParameterFibreKernel.AssignmentVector p)
    (hc : calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w = true)
    (hclear : (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w).2 = true) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w vector hc
    let view := (nativeSourceCell rate rewards C_star C_h q z).selected.view
    (calendarRecorderFastKernel rate rewards C_star C_h control0 q (past k hk.le w) vector).map Prod.snd =
      (ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate view.payload.anchor
        (scoreWeight Q (nativeBefore rate rewards C_star C_h control0 q z)) view.payload.anchor_pos
        (RecordedSlowRefresh.scoreWeight_pos Q _) view.payload.slowSet).toMeasure.map (fun j => some j.val) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let z := calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk w vector hc
  let view := (nativeSourceCell rate rewards C_star C_h q z).selected.view
  obtain ⟨valid, _hrates, _hbottom, hm⟩ := calendarRecorderFastKernel_marginals
    rate rewards C_star C_h control0 b0 u0 t0 k hk w vector hc
  have hcomp := ReferenceGeneratedCalendarRoundLaw.calendarInvocationCell_numerical_complement
    rate rewards C_star C_h control0 b0 u0 t0 k hk w vector hc hclear
  have hpmf := choiceFastPMF_eq_collection rate q view valid (nativeBefore rate rewards C_star C_h control0 q z) hcomp
  exact hm.trans (congrArg (fun pmf : PMF (FastArm view.payload.slowSet) =>
    pmf.toMeasure.map (fun j => some j.val)) hpmf)

end GeneratedLive


section RootFast

open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInstallationCellFactors

/-- FAST from the actual first-invocation common-update draw, after forgetting
recorder and UPDATE. The fixed whole assignment vector is kept by that draw. -/
theorem root_fast_draw_marginal (t : Fin p.T)
    (z : FirstInvocationSource rate rewards C_star C_h t)
    (hclear : (firstBefore rate rewards C_star C_h control0 t z).overflow = false) :
    let view := (firstSourceCell rate rewards C_star C_h t z).selected.view
    (ContinuousLearningRows.timeControlLaw p).map
      (fun c => (firstPairUpdateDraw rate rewards C_star C_h control0 t z c).1.2) =
      (ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate view.payload.anchor
        (scoreWeight Q (firstBefore rate rewards C_star C_h control0 t z)) view.payload.anchor_pos
        (RecordedSlowRefresh.scoreWeight_pos Q _) view.payload.slowSet).toMeasure.map (fun j => some j.val) := by
  dsimp only
  let view := (firstSourceCell rate rewards C_star C_h t z).selected.view
  let valid := ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
    rate rewards C_star C_h t z.val view (actualFirstCell_view rate rewards C_star C_h control0 t z)
  let K := ReferenceRankInstallationSourceKernelComposition.installationRecorderFastOutputKernel rate t view valid
  have hdraw : (ContinuousLearningRows.timeControlLaw p).map
      (fun c => (firstPairUpdateDraw rate rewards C_star C_h control0 t z c).1.2) = K.map Prod.snd := by
    calc
      _ = ((ContinuousLearningRows.timeControlLaw p).map
          (firstPairUpdateDraw rate rewards C_star C_h control0 t z)).map
          (fun y : ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p => y.1.2) :=
        (Measure.map_map measurable_fst.snd
          (measurable_firstPairUpdateDraw rate rewards C_star C_h control0 t z)).symm
      _ = _ := by
        rw [firstPairUpdateDraw_law, ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel,
      Measure.map_map measurable_fst.snd
        (ReferenceRankInstallationCommonUpdateJointLaw.measurable_commonUpdateKernelMap rate rewards t view
          (ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
            rate rewards C_star C_h control0 t z.val))]
        rfl
  have hm := (ReferenceRankInstallationSourceKernelComposition.installationRecorderFastOutputKernel_marginals
    rate t view valid).2
  have hslow : SnapshotRecordingKernel.assignmentSlowSet p view.payload.assignment = view.payload.slowSet := by
    apply Subtype.ext
    exact view.payload.assignment_image
  rw [hslow] at hm
  have hcomp := ReferenceGeneratedCalendarRootRoundLaw.rootSource_numerical_complement
    rate rewards C_star C_h control0 t z hclear
  have hpmf := choiceFastPMF_eq_collection rate t view valid (firstBefore rate rewards C_star C_h control0 t z) hcomp
  exact hdraw.trans (hm.trans (congrArg (fun pmf : PMF (FastArm view.payload.slowSet) =>
    pmf.toMeasure.map (fun j => some j.val)) hpmf))

end RootFast


section CollectionFast

open ReferencePostInvocationCollectionNativeLaw

/-- Enabled clear COLLECTION tests retain the arbitrary actual incoming U.
The recorder/proposal/refresh are integrated out using the native pair marginal. -/
theorem collection_source_fast_test (q : Fin p.T)
    (z : CollectionDateSource rate rewards C_star C_h q) (U : SlowSet p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (hen : (collectionInput rate rewards C_star C_h q z).enabled = true)
    (hclear : (collectionBefore rate rewards C_star C_h q z).overflow = false)
    (f : SlowSet p × Fin p.K → ℝ≥0∞) :
    let P := (collectionArguments rate rewards C_star C_h q z).1
    (∫⁻ y : ContinuousLearningRows.TimeControl p × (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar),
      match laterCollectionCell? rate rewards C_star C_h q
        (replaceCollectionSource rate rewards C_star C_h control0 q z y.1) U
        (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a y.2) with
      | none => 0
      | some e => f (e.slowSet, e.fastArm)
      ∂(ContinuousLearningRows.timeControlLaw p).prod
        (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)) =
      ∑ j : FastArm U, f (U, j.val) * collectionFastPMF rate P.anchor
        (scoreWeight Q (collectionBefore rate rewards C_star C_h q z)) P.anchor_pos
        (RecordedSlowRefresh.scoreWeight_pos Q _) U j := by
  dsimp only
  let pair := nativePair rate rewards C_star C_h q z U
  let test : FastArm U → ℝ≥0∞ := fun j => f (U, j.val)
  have hp := measurable_nativePair rate rewards C_star C_h q z U
  have ht : Measurable test := measurable_of_finite _
  have htest : Measurable (fun c => test (pair c).2) := ht.comp (measurable_snd.comp hp)
  have he (y : ContinuousLearningRows.TimeControl p ×
      (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar)) :
      (match laterCollectionCell? rate rewards C_star C_h q
        (replaceCollectionSource rate rewards C_star C_h control0 q z y.1) U
        (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a y.2) with
      | none => 0
      | some e => f (e.slowSet, e.fastArm)) = test (pair y.1).2 := by
    have hf : ReferenceSourceFastScalarDisintegration.sourceFastScalar p q
        (replaceCollectionSource rate rewards C_star C_h control0 q z y.1).val =
        y.1.1 ContinuousControlSlice.Label.fast := by
      simp only [replaceCollectionSource, ReferenceSourceFastScalarDisintegration.sourceFastScalar,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, Function.update_self]
    unfold laterCollectionCell?
    rw [collectionEnabled_replace_control, hen]
    simp only [ite_true, laterCollectionCell, collectionBefore_replace_control,
      collectionPayload_replace_control, hclear, Bool.false_eq_true, ite_false, hf, test, pair, nativePair]
  trans ∫⁻ y : ContinuousLearningRows.TimeControl p ×
      (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar), test (pair y.1).2
      ∂(ContinuousLearningRows.timeControlLaw p).prod
        (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)
  · exact lintegral_congr he
  rw [lintegral_prod (fun y : ContinuousLearningRows.TimeControl p ×
    (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar) => test (pair y.1).2)
    (htest.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  have hmap : (ContinuousLearningRows.timeControlLaw p).map (fun c => (pair c).2) =
      (collectionFastPMF rate (collectionArguments rate rewards C_star C_h q z).1.anchor
        (scoreWeight Q (collectionBefore rate rewards C_star C_h q z))
        (collectionArguments rate rewards C_star C_h q z).1.anchor_pos
        (RecordedSlowRefresh.scoreWeight_pos Q _) U).toMeasure := by
    have hpair := nativePair_map rate rewards C_star C_h control0 q z U hen
    have hs := congrArg (fun mu => mu.map Prod.snd) hpair
    rw [Measure.map_map measurable_snd hp, Measure.map_snd_prod] at hs
    simpa only [measure_univ, one_smul, pair, Function.comp_def] using hs
  calc
    _ = ∫⁻ j, test j ∂(ContinuousLearningRows.timeControlLaw p).map (fun c => (pair c).2) :=
      (lintegral_map ht (measurable_snd.comp hp)).symm
    _ = _ := by
      rw [hmap, lintegral_fintype]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j)]

end CollectionFast


section GeneratedCollection

open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarRoundInnovation
open ReferenceGeneratedCalendarNoncallRoundLaw

variable (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "stored" => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0

/-- The COLLECTION refill with the SAME accepted history and literal stored
incoming U. No distributional assertion about that U is used. -/
theorem calendar_collection_fast_refill_test (s : Fin p.T) (k : ℕ)
    (hk : t0.val + 1 + k < p.T) (hs : s.val ≤ t0.val + 1 + k) (w : Sample k)
    (hlive : current k hk.le w ∉ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩)
    (hcol : current k hk.le w ∈ collectionDateDomain rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩)
    (hen : (collectionInput rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
      ⟨current k hk.le w, hcol⟩).enabled = true)
    (hclear : (collectionBefore rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
      ⟨current k hk.le w, hcol⟩).overflow = false)
    (Phi : History rate s ⟨t0.val + 1 + k, hk⟩ × (SlowSet p × Fin p.K) → ℝ≥0∞) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
      (by change t0.val < t0.val + 1 + k; omega) k
    let H := calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le w
    let zz : CollectionDateSource rate rewards C_star C_h q := ⟨current k hk.le w, hcol⟩
    let P := (collectionArguments rate rewards C_star C_h q zz).1
    let U := (stored k hk.le w).1
    (∫⁻ x, match calendarNoncallCell rate rewards C_star C_h control0 b0 u0 t0 k hk (fill (w, x)) with
      | none => 0
      | some e => Phi (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le
          (fill (w, x)), (e.slowSet, e.fastArm))
      ∂ReferencePostInvocationSupportedDisintegration.innovationLaw (p := p)) =
      ∑ j : FastArm U, Phi (H, (U, j.val)) *
        ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate P.anchor
          (scoreWeight Q (collectionBefore rate rewards C_star C_h q zz)) P.anchor_pos
          (RecordedSlowRefresh.scoreWeight_pos Q _) U j := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let zz : CollectionDateSource rate rewards C_star C_h q := ⟨current k hk.le w, hcol⟩
  have h := collection_source_fast_test rate rewards C_star C_h control0 q zz (stored k hk.le w).1
    (original k w).1.2 hen hclear
    (fun v => Phi (calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s q k hk.le w, v))
  refine Eq.trans ?_ h
  apply lintegral_congr
  intro x
  rw [calendarNoncallCell_fill_collection rate rewards C_star C_h control0 b0 u0 t0 k hk w hlive hcol x,
    calendarSourceHistory_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 s k hk hs w x]

end GeneratedCollection


section BeforeFirstCall

open ReferenceGeneratedCalendarEpisodePrefixRecombination
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarPathAgreement

private theorem noCallBefore_first_date (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u t)
    (n : Fin (p.T + 1))
    (hn : ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore rate rewards C_star C_h n z) :
    n.val ≤ t.val := by
  by_contra h
  have ht : t.val < n.val := by omega
  have hb := (ReferenceFirstCollectionPrecallCalendarSupport.before_cut_iff_no_call_through
    rate rewards C_star C_h t z).mpr (fun v hv =>
      (ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none rate rewards C_star C_h v z).mp
        (hn v (hv.trans_lt ht)))
  rw [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
    rate rewards C_star C_h u t z hz] at hb
  exact (Nat.lt_irrefl _ hb)

/-- Before the first call, including a possible call at the boundary itself,
the terminal strict physical prefix is the SAME original strict prefix. -/
theorem terminalSource_prefix_beforeFirstCall (n : Fin (p.T + 1)) (w : Omega)
    (hw : w ∈ beforeFirstCall rate rewards C_star C_h n) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val (Z w) = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h w) := by
  rcases w with ⟨i, w⟩
  cases i with
  | noCall => rfl
  | stopped u t => rfl
  | generated b u t =>
    have hz : (calendarOriginalLift rate rewards C_star C_h b u t (p.T - (t.val + 1)) w).1.1.val ∈
        ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u t := by
      cases b with
      | false => exact (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_facts
          rate rewards C_star C_h u t _
          (calendarOriginalLift rate rewards C_star C_h false u t _ w).1.1.property).1
      | true => exact (calendarOriginalLift rate rewards C_star C_h true u t _ w).1.1.property.1
    have hnt := noCallBefore_first_date rate rewards C_star C_h u t _ hz n hw
    have hp := congrArg (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val)
      (ReferenceGeneratedCalendarEpisodeInitialLaw.generated_sourcePrefix_root
        rate rewards C_star C_h control0 b u t w)
    change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val
      (Z ⟨.generated b u t, w⟩) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val
        (calendarOriginalLift rate rewards C_star C_h b u t (p.T - (t.val + 1)) w).1.1.val
    exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 n.val t.val hnt _).symm.trans
      (hp.trans (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 n.val t.val hnt _))

omit rewards C_star C_h control0 in
private theorem filter_time_twice (L : List (LogicalCell p rate)) (a b : ℕ) (hab : a ≤ b) :
    (L.filter (fun e => e.time.val < b)).filter (fun e => e.time.val < a) =
      L.filter (fun e => e.time.val < a) := by
  rw [List.filter_filter]
  congr 1
  funext e
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨And.left, fun h => ⟨h, h.trans_le hab⟩⟩

omit rewards C_star C_h control0 in
private theorem find_time_strict_filter (L : List (LogicalCell p rate)) (v : Fin p.T)
    (n : ℕ) (hv : v.val < n) :
    (L.filter (fun e => e.time.val < n)).find? (fun e => e.time == v) =
      L.find? (fun e => e.time == v) := by
  rw [List.find?_filter]
  congr 1
  funext e
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]
  exact ⟨And.right, fun h => ⟨h ▸ hv, h⟩⟩

/-- The accepted sourceEstimateHistory is an explicit projection of the
already accepted strict observer. The current call, if any, is not excluded. -/
theorem sourceEstimateHistory_beforeFirstCall (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (w : Omega) (hw : w ∈ beforeFirstCall rate rewards C_star C_h q.castSucc) :
    sourceEstimateHistory rate rewards C_star C_h control0 s q w =
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val (prefixObservation rate rewards C_star C_h control0 q.castSucc w).1,
        (prefixObservation rate rewards C_star C_h control0 q.castSucc w).2.2.filter
          (fun e => e.time.val < s.val)),
        fun v => sourceOptionalEstimate rate
          ((prefixObservation rate rewards C_star C_h control0 q.castSucc w).2.2.find? (fun e => e.time == v.val))) := by
  have hp := terminalSource_prefix_beforeFirstCall rate rewards C_star C_h control0 q.castSucc w hw
  have hs := congrArg (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val) hp
  simp only [Fin.val_castSucc, ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 s.val q.val hsq] at hs
  apply Prod.ext
  · apply Prod.ext
    · change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val (Z w) =
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val
            (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h w))
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 s.val q.val hsq]
      exact hs
    · change (archive rate rewards C_star C_h control0 w).filter (fun e => e.time.val < s.val) =
        ((archive rate rewards C_star C_h control0 w).filter (fun e => e.time.val < q.val)).filter
          (fun e => e.time.val < s.val)
      exact (filter_time_twice rate (archive rate rewards C_star C_h control0 w) s.val q.val hsq).symm
  · funext v
    change sourceOptionalEstimate rate (currentMark rate rewards C_star C_h control0 v.val w) = _
    apply congrArg (sourceOptionalEstimate rate)
    exact (find_time_strict_filter rate (archive rate rewards C_star C_h control0 w) v.val q.val v.property.2).symm

end BeforeFirstCall

section RootHistory

open ReferenceGeneratedRankCalendarFoundation ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarPathAgreement ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarRootRoundLaw ReferenceFirstNextInstallationCellFactors
open ReferenceFirstNextInstallationTransitionLaw ReferenceFirstLiveActualRefreshTestLaw

variable (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Root" => CalendarSample rate rewards C_star C_h b0 u0 t0 0
local notation "rootCell" => calendarRootCell rate rewards C_star C_h control0 b0 u0 t0
local notation "rootHistory" => calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0
local notation "Event" => ReferencePostInvocationPrefixLocality.branchEvent rate rewards C_star C_h b0 u0 t0
local notation "restore" => rootRestore rate rewards C_star C_h control0 b0 u0 t0
local notation "installed" => rootInstalledSource rate rewards C_star C_h b0 u0 t0

/-- ROOT contributes no current cell to the accepted strict estimate history. -/
theorem calendarSourceHistory_root_past (s : Fin p.T) (hs : s.val ≤ t0.val) (w : Root) :
    rootHistory s t0 0 (by omega) w =
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val
          (calendarRootPast rate rewards C_star C_h control0 b0 u0 t0 w).1,
        (calendarRootPast rate rewards C_star C_h control0 b0 u0 t0 w).2.2.filter
          (fun e => e.time.val < s.val)),
        fun v => sourceOptionalEstimate rate
          ((calendarRootPast rate rewards C_star C_h control0 b0 u0 t0 w).2.2.find?
            (fun e => e.time == v.val))) := by
  have ht : (rootCell w).time = t0 := by
    cases b0 <;> exact actualFirstCell_time rate rewards C_star C_h control0 t0 _ _
  have hstored := (calendarObservation_root rate rewards C_star C_h control0 b0 u0 t0 (by omega) w).2.1
  unfold calendarSourceHistory calendarRootPast
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 s.val t0.val hs, hstored]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · simp only [List.filter_append, List.filter_cons, List.filter_nil, ht,
        decide_eq_false (by omega : ¬t0.val < s.val), Bool.false_eq_true, ite_false, List.append_nil]
  · funext v
    apply congrArg (sourceOptionalEstimate rate)
    rw [List.find?_append]
    have hne : ¬t0 = v.val := by intro he; have := v.property.2; rw [← he] at this; omega
    simp only [List.find?_cons, List.find?_nil, ht, beq_eq_false_iff_ne.mpr hne, Option.or_none]

/-- Evaluation of ROOT FAST after the actual assignment fibre. The complete
original vector, private remainder, archive and incoming set are retained. -/
theorem generated_component_root_fast_test (ids : Option (CompletePublicTable.IDArray p))
    (s : Fin p.T) (hs : s.val ≤ t0.val)
    (Phi : History rate s t0 × (SlowSet p × Fin p.K) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w, (currentMark rate rewards C_star C_h control0 t0 ⟨.generated b0 u0 t0, w⟩).elim 0
      (fun e => if e.before.overflow = false then
        Phi (sourceEstimateHistory rate rewards C_star C_h control0 s t0 ⟨.generated b0 u0 t0, w⟩,
          (e.slowSet, e.fastArm)) else 0)
      ∂ids.elim
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b0 u0 t0))
        (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
          rate rewards C_star C_h control0 id (.generated b0 u0 t0))) =
    ∑ q : Fin (M p), ∫⁻ r : ReferenceFirstNextInstallationTransitionLaw.EventRemainder control0 t0 Event q,
      ∫⁻ a : ErasedAuxiliaryArray t0, ∫⁻ v : AssignmentParameterFibreKernel.AssignmentVector p,
        let w0 := restore q r a v control0 scalarZero
        let z0 := installed (ReferenceFirstNextInstallationTransitionLaw.restoreEventSource control0 t0 Event
          (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, control0)) v
        let view := (firstSourceCell rate rewards C_star C_h t0 z0).selected.view
        if (firstBefore rate rewards C_star C_h control0 t0 z0).overflow = false then
          ∑ j : FastArm view.payload.slowSet,
            ids.elim (Phi (rootHistory s t0 0 (by omega) w0, (view.payload.slowSet, j.val)))
              (fun id => (CompletePublicTable.idArrayMeasure p {id})⁻¹ *
                (if (rootHistory s t0 0 (by omega) w0).1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection id
                then Phi (rootHistory s t0 0 (by omega) w0, (view.payload.slowSet, j.val)) else 0)) *
              ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate view.payload.anchor
                (scoreWeight Q (firstBefore rate rewards C_star C_h control0 t0 z0)) view.payload.anchor_pos
                (RecordedSlowRefresh.scoreWeight_pos Q _) view.payload.slowSet j
        else 0
        ∂rootVectorKernel rate rewards C_star C_h control0 b0 u0 t0
          (ReferenceFirstNextInstallationTransitionLaw.restoreEventSource control0 t0 Event
            (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, control0),
            (rootUpdateSplit b0 t0).symm (a, scalarZero))
        ∂erasedAuxiliaryLaw t0
        ∂ReferenceFirstNextInstallationTransitionLaw.eventRemainderLaw control0 t0 Event q := by
  let F : History rate s t0 × (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞ :=
    fun y => y.2.2.elim 0 (fun e => if e.before.overflow = false then Phi (y.1, (e.slowSet, e.fastArm)) else 0)
  have hF : Measurable F := (measurable_clearFast_test rate s t0 Phi hPhi).comp
    (measurable_snd.snd.prodMk measurable_fst)
  have ht := generated_component_source_joint_native_root_test rate rewards C_star C_h control0
    b0 u0 t0 ids s hs F hF
  let Psi : History rate s t0 × (SlowSet p × Fin p.K) → ℝ≥0∞ := fun y => ids.elim (Phi y)
    (fun id => (CompletePublicTable.idArrayMeasure p {id})⁻¹ *
      (if y.1.1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection id then Phi y else 0))
  have hPsi : Measurable Psi := by
    cases ids with
    | none => exact hPhi
    | some id => exact measurable_const.mul (hPhi.ite
        ((ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection id).preimage measurable_fst.fst.fst) measurable_const)
  let f : Root → ℝ≥0∞ := fun w => if (rootCell w).before.overflow = false then
    Psi (rootHistory s t0 0 (by omega) w, ((rootCell w).slowSet, (rootCell w).fastArm)) else 0
  have hf : Measurable f := (measurable_clearFast_test rate s t0 Psi hPsi).comp
    ((measurable_calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s).snd.snd.prodMk
      (measurable_calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0 s t0 0 (by omega)))
  refine ht.trans (Eq.trans (b := ∫⁻ w, f w
    ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 0 (by omega)) ?_ ?_)
  · change (∫⁻ w, F (calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s w)
        ∂ids.elim (calendarLaw rate rewards C_star C_h control0 b0 u0 t0 0 (by omega))
          (fun id => (CompletePublicTable.idArrayMeasure p {id})⁻¹ •
            (calendarLaw rate rewards C_star C_h control0 b0 u0 t0 0 (by omega)).restrict
              ((calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 0 (by omega)) ⁻¹'
                ReferenceFixedIDSourceSection.fixedIDSourceSection id))) =
      ∫⁻ w, f w ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 0 (by omega)
    cases ids with
    | none => rfl
    | some id =>
      have hID := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection id).preimage
        (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 0 (by omega))
      have hi := (hF.comp
        (measurable_calendarRootSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s)).indicator hID
      simp only [Function.comp_def] at hi
      rw [Option.elim_some, lintegral_smul_measure, ← lintegral_indicator hID, smul_eq_mul,
        ← lintegral_const_mul _ hi]
      apply lintegral_congr
      intro w
      let value := Phi (rootHistory s t0 0 (by omega) w, ((rootCell w).slowSet, (rootCell w).fastArm))
      change (CompletePublicTable.idArrayMeasure p {id})⁻¹ *
          (if (rootHistory s t0 0 (by omega) w).1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection id
          then (if (rootCell w).before.overflow = false then value else 0) else 0) =
        if (rootCell w).before.overflow = false then (CompletePublicTable.idArrayMeasure p {id})⁻¹ *
          (if (rootHistory s t0 0 (by omega) w).1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection id
          then value else 0) else 0
      split_ifs <;> simp only [mul_zero]
  · rw [calendarLaw_root_refill_test rate rewards C_star C_h control0 b0 u0 t0 f hf]
    apply Finset.sum_congr rfl
    intro q _
    apply lintegral_congr
    intro r
    apply lintegral_congr
    intro a
    apply lintegral_congr
    intro v
    dsimp only
    let w0 := restore q r a v control0 scalarZero
    let z0 := installed (ReferenceFirstNextInstallationTransitionLaw.restoreEventSource control0 t0 Event
      (rootEvent_control_invariant rate rewards C_star C_h control0 b0 u0 t0) q (r, control0)) v
    let view := (firstSourceCell rate rewards C_star C_h t0 z0).selected.view
    have hpre (c : ContinuousLearningRows.TimeControl p) (x : ContinuousControlSlice.Scalar) :
        (rootCell (restore q r a v c x)).before = firstBefore rate rewards C_star C_h control0 t0 z0 := by
      rw [rootRestore_cell]
      change firstBefore rate rewards C_star C_h control0 t0 _ = _
      have hp := congrArg (fun z : RootPast rate => z.1)
        (congrArg Prod.fst (rootRestore_assignedPast_nonuse rate rewards C_star C_h control0 b0 u0 t0 q r a v c x))
      dsimp only [calendarRootAssignedPast, calendarRootPast] at hp
      rw [rootRestore_currentSource, rootRestore_currentSource] at hp
      have hn := congrArg
        (ReferenceFirstCollectionCurrentRetainedGate.prefixReadout? rate rewards C_star C_h t0) hp
      have he := Option.some.inj ((firstBefore_spec rate rewards C_star C_h control0 t0 _).symm.trans
        (hn.trans (firstBefore_spec rate rewards C_star C_h control0 t0 z0)))
      exact congrArg (fun S : ReferenceRankInstallationPostUpdateProposalLaw.NumericalState p =>
        (⟨S.1, S.2.1, S.2.2⟩ : RecordedQueueRun.RunState p.K)) he
    by_cases hclear : (firstBefore rate rewards C_star C_h control0 t0 z0).overflow = false
    · rw [ite_eq_left hclear]
      let test : Option (Fin p.K) → ℝ≥0∞ := fun j => j.elim 0
        (fun j => Psi (rootHistory s t0 0 (by omega) w0, (view.payload.slowSet, j)))
      have ht : Measurable test := measurable_of_countable _
      have heval (c : ContinuousLearningRows.TimeControl p) (x : ContinuousControlSlice.Scalar) :
          f (restore q r a v c x) = test (firstPairUpdateDraw rate rewards C_star C_h control0 t0 z0 c).1.2 := by
        have hp := congrArg Prod.fst (rootRestore_assignedPast_nonuse
          rate rewards C_star C_h control0 b0 u0 t0 q r a v c x)
        dsimp only [calendarRootAssignedPast] at hp
        have hH : rootHistory s t0 0 (by omega) (restore q r a v c x) =
            rootHistory s t0 0 (by omega) w0 := by
          rw [calendarSourceHistory_root_past rate rewards C_star C_h control0 b0 u0 t0 s hs,
            calendarSourceHistory_root_past rate rewards C_star C_h control0 b0 u0 t0 s hs, hp]
        have hU := congrArg (fun z : RootPast rate => z.2.1) hp
        have hpair := congrArg (fun y : ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p × Bool => y.1.1.2)
          (rootRestore_control rate rewards C_star C_h control0 b0 u0 t0 q r a v c x)
        dsimp only [calendarRootPast] at hU
        change ReferenceRankInstallationRecorderFastLaw.actualReservedFast rate rewards C_star C_h t0
          (calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 0 (by omega) (restore q r a v c x)) =
          (firstPairUpdateDraw rate rewards C_star C_h control0 t0 z0 c).1.2 at hpair
        have hfast : some (rootCell (restore q r a v c x)).fastArm =
            (firstPairUpdateDraw rate rewards C_star C_h control0 t0 z0 c).1.2 := by
          rw [← hpair, rootRestore_currentSource, rootRestore_cell]
          change some (if (firstBefore rate rewards C_star C_h control0 t0 _).overflow then _ else _) = _
          have hc' := (congrArg RecordedQueueRun.RunState.overflow (hpre c x)).trans hclear
          rw [rootRestore_cell] at hc'
          change (firstBefore rate rewards C_star C_h control0 t0 _).overflow = false at hc'
          rw [hc']
          simp only [Bool.false_eq_true, ite_false]
          exact (firstSourceCell_fast rate rewards C_star C_h control0 t0 _).symm
        have hU0 : (rootCell w0).slowSet = view.payload.slowSet := by
          rw [rootRestore_cell]
          change (if (firstBefore rate rewards C_star C_h control0 t0 z0).overflow then _ else _) = _
          simp only [hclear, Bool.false_eq_true, ite_false]
          rfl
        dsimp only [f]
        rw [hpre, ite_eq_left hclear, hH, hU, hU0, ← hfast]
        rfl
      simp_rw [heval, lintegral_const, measure_univ, mul_one]
      rw [← lintegral_map ht ((measurable_firstPairUpdateDraw rate rewards C_star C_h control0 t0 z0).fst.snd),
        root_fast_draw_marginal rate rewards C_star C_h control0 t0 z0 hclear,
        lintegral_map ht (measurable_of_finite (fun j : FastArm view.payload.slowSet => some j.val)),
        lintegral_fintype]
      apply Finset.sum_congr rfl
      intro j _
      rw [PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j)]
      rfl
    · rw [ite_eq_right hclear]
      have heval (c : ContinuousLearningRows.TimeControl p) (x : ContinuousControlSlice.Scalar) :
          f (restore q r a v c x) = 0 := by dsimp only [f]; rw [hpre, ite_eq_right hclear]
      simp_rw [heval, lintegral_zero]

end RootHistory

end Bandits.Support.ReferenceGeneratedCalendarRetainedFastCore
