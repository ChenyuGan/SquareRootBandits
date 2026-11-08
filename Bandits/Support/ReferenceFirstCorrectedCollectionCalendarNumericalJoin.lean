/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedAllArmSegmentFinalNumericalJoin
public import Bandits.Support.ReferenceFirstCorrectedReplacementCollectionReadout

/-!
# Calendar synchronization at the first corrected collection

Internal joins for ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`. The calendar retains every physical date,
including disabled rounds and enabled rounds with zero arrival.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstCorrectedCollectionCalendarNumericalJoin

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction ReferenceLaterCollectionArrivalReadout
open ReferenceCollectionRawBufferHistory RecordedQueueRun

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem live_readout_zero (s : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (c : RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
  obtain ⟨selected, ho, hselection, hbase, hlive, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some s r c hc
  have hz : 0 < selected.view.payload.sigma.val := by omega
  unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
  simp only [hselection, hz, hlive, and_self, ite_true, dite_eq_left ho]
  exact congrArg some hcell.symm

private theorem collection_readout_zero (s : ℕ)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : RoundInput p.K)
    (hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some cell := by
  open ReferenceLaterCollectionArrivalReadout in
  have hp : (laterCollectionReadout s record).isSome = true := by rw [hread]; rfl
  obtain ⟨hf, hb⟩ := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain s record).mp hp
  cases hcoord : record.output.preparation.coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            dite_eq_left hf, hcoord] using hread
      | _ => simp only [hcoord] at hb
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
          have hg : s < registers.payload.sigma.val := by simpa only [hcoord] using hb
          have hg0 : 0 < registers.payload.sigma.val := by omega
          simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            dite_eq_left hf, hcoord, hg, hg0, ite_true] using hread
      | _ => simp only [hcoord] at hb
  | first outcome => cases outcome <;> simp only [hcoord] at hb
  | invalidCollectionCutoff => simp only [hcoord] at hb
  | dagger => simp only [hcoord] at hb

private theorem collection_readout_disabled (s : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K)
    (hread : laterCollectionReadout s r = some c) (hdisabled : c.enabled = false) :
    c.recordedArm = none ∧ ∀ a, RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0 := by
  classical
  have hmarker : c.recordedArm = none := by
    unfold laterCollectionReadout at hread
    split at hread
    next =>
      cases hc : r.output.preparation.coordinator with
      | first outcome => cases outcome <;> simp [hc] at hread
      | invalidCollectionCutoff => simp [hc] at hread
      | dagger => simp [hc] at hread
      | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp only [hc] at hread
        all_goals try contradiction
        next core snapshot hcontinue selected =>
          cases Option.some.inj hread
          change (SnapshotRecordingKernel.recordingMap p .collection _ _ _ _ _ _ _ _ _ _ _) = none
          change (continuingCollectionInput r payload ledger clock cutoff snapshot).enabled = false at hdisabled
          dsimp only [continuingCollectionInput] at hdisabled
          rw [hdisabled]
          exact SnapshotRecordingKernel.recordingMap_disabled ..
      | live registers owned base outcome =>
        cases outcome <;> simp only [hc] at hread
        all_goals try contradiction
        next dispatched hs ledger hi he hd hclock hp hn selected =>
          split at hread
          next =>
            cases Option.some.inj hread
            change (SnapshotRecordingKernel.recordingMap p .collection _ _ _ _ _ _ _ _ _ _ _) = none
            change (laterCutoffCollectionInput r registers owned base dispatched selected).enabled = false at hdisabled
            dsimp only [laterCutoffCollectionInput] at hdisabled
            rw [hdisabled]
            exact SnapshotRecordingKernel.recordingMap_disabled ..
          next => contradiction
    next => contradiction
  refine ⟨hmarker, ?_⟩
  intro a
  simp only [RecordedQueueRun.quantizedArrival, hmarker, reduceCtorEq, ite_false]

private theorem cell0_of_live (s : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (c : RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c) :
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
  simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0,
    live_readout_zero s r c hc, Option.some_or]

private theorem cell0_of_collection (s : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (c : RoundInput p.K)
    (hc : laterCollectionReadout s r = some c) :
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
  have hzero := collection_readout_zero s r c hc
  have hnone : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none := by
    cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
    | none => rfl
    | some d =>
      exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint rate 0 r
        ⟨by rw [hl]; rfl, by rw [hzero]; rfl⟩)
  simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hnone, Option.none_or, hzero]

private theorem cell0_disabled
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (c : RoundInput p.K)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c)
    (hdisabled : c.enabled = false) :
    c.recordedArm = none ∧ ∀ a, quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0 := by
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
  | none =>
    have hr : laterCollectionReadout 0 r = some c := by
      simpa only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hl, Option.none_or] using hc
    exact collection_readout_disabled 0 r c hr hdisabled
  | some d =>
    have heq : d = c := Option.some.inj (by
      simpa only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hl, Option.some_or] using hc)
    subst d
    have he := (ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 r c hl).1
    rw [hdisabled] at he
    contradiction

private theorem tagged_readout_of_cell0
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (c : RoundInput p.K)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c) :
    (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r).map (Sum.elim id id) =
      some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c) := by
  have hp := ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 r
  cases ht : ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r with
  | none =>
    cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r <;>
      cases hr : laterCollectionReadout 0 r <;>
      simp_all [ReferenceCompleteNumericalBranchObservation.leftProjection,
        ReferenceCompleteNumericalBranchObservation.rightProjection,
        ReferenceFirstCollectionCurrentRetainedGate.cell0]
  | some tag =>
    cases tag <;>
      cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r <;>
      cases hr : laterCollectionReadout 0 r <;>
      simp_all [ReferenceCompleteNumericalBranchObservation.leftProjection,
        ReferenceCompleteNumericalBranchObservation.rightProjection,
        ReferenceFirstCollectionCurrentRetainedGate.cell0]

private theorem mapM_id_some {α : Type*} (slots : List (Option α)) (cells : List α)
    (h : slots.mapM id = some cells) : slots = cells.map some := by
  induction slots generalizing cells with
  | nil =>
    have he : cells = [] := (Option.some.inj h).symm
    subst cells
    rfl
  | cons slot slots ih =>
    cases slot with
    | none => simp [List.mapM_cons] at h
    | some a =>
      cases ht : slots.mapM id with
      | none => simp [List.mapM_cons, ht] at h
      | some tail =>
        have he : a :: tail = cells := by simpa [List.mapM_cons, ht] using h
        rw [← he, List.map_cons, ← ih tail ht]

/-- Successful optional coverage identifies every chronological slot, rather
than merely the number of retained cells. -/
private theorem prefixInputs_readout
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (q : ℕ) (G : List (RoundInput p.K))
    (hlen : G.length = q)
    (hq : q ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + q) z = some G) :
    ∀ k : Fin q,
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]'(by omega)) =
          some (G[k.val]'(by omega)) := by
  have hs := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h _ z G hprefix
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
    ite_eq_left hs, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
    Nat.add_sub_cancel_left] at hprefix
  have hmap := mapM_id_some _ G hprefix
  intro k
  have he := congrArg (fun L => L[k.val]?) hmap
  simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
    List.getElem?_map, List.getElem?_take, show k.val < q from k.isLt, ite_true,
    List.getElem?_eq_getElem (show k.val <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length by omega),
    List.getElem?_eq_getElem (show k.val < G.length by omega), Option.map_some, Option.some.injEq] using he

/-- Append a whole retained physical segment without dropping absent slots.
The optional cells are explicit pointwise inputs to this list lemma. -/
private theorem prefixInputs_append_records
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (e : ℕ)
    (A D : List (RoundInput p.K))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e) z = some A)
    (hD : D.length = records.length)
    (hrecords : ∀ j : Fin records.length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[e + j.val]? =
        some records[j.val])
    (hcells : ∀ j : Fin records.length,
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate records[j.val] =
        some (D[j.val]'(by omega))) :
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
          (e + records.length)) z = some (A ++ D) := by
  induction records generalizing e A D with
  | nil =>
    have hd : D = [] := List.length_eq_zero_iff.mp (by simpa only [List.length_nil] using hD)
    simpa only [List.length_nil, Nat.add_zero, hd, List.append_nil] using hprefix
  | cons r records ih =>
    cases D with
    | nil => simp only [List.length_nil, List.length_cons] at hD; omega
    | cons c D =>
      have hr := hrecords ⟨0, by simp only [List.length_cons]; omega⟩
      have hc := hcells ⟨0, by simp only [List.length_cons]; omega⟩
      simp only [Nat.add_zero, List.getElem_cons_zero] at hr hc
      have hnext := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e)
        z A hprefix r c (by
          simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart,
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
            Nat.add_sub_cancel_left] using hr) hc
      have htail := ih (e + 1) (A ++ [c]) D (by
          simpa only [Nat.add_assoc] using hnext)
        (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hD)
        (fun j => by
          simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hrecords ⟨j.val + 1, by simpa only [List.length_cons] using Nat.succ_lt_succ j.isLt⟩)
        (fun j => by
          simpa only [List.getElem_cons_succ]
            using hcells ⟨j.val + 1, by simpa only [List.length_cons] using Nat.succ_lt_succ j.isLt⟩)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc, List.cons_append, List.nil_append] using htail

/-- The actual checked input has the canonical cell's literal queue input.
Both the enabled bit and disabled zero are needed for this statement. -/
private theorem completed_queue_record
    (l0 : Ledger rate) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (done : CompletedRound rate) (c : RoundInput p.K)
    (hextract : extractRound r = some done)
    (hsigma : done.context.preLedger.sigma = l0.sigma)
    (hcutoff : done.context.preLedger.cutoff = l0.cutoff)
    (hfreeze : done.context.preLedger.freezeAt = l0.freezeAt)
    (henabled : c.enabled = collectionEnabled l0 r.input.time)
    (hdate : c.enabled = decide (r.input.time.val + 1 < l0.freezeAt))
    (harrival : ∀ a, CoordinatorCollectionLedger.localArrival (rawDiagnostic r) a =
      quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)
    (hdisabled : c.enabled = false → ∀ a,
      quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0)
    (a : Fin p.K) :
    CoordinatorCollectionLedger.localQueueRecord l0 done.input.round done.input.enabled done.input.raw a =
      (c.enabled, quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) := by
  classical
  obtain ⟨hraw, he⟩ := actual_completed_input_raw_and_enabled r done hextract
  have hround := (actual_collection_round_checked r done hextract).2.1
  have heq : done.input.enabled = c.enabled := by
    rw [he, henabled]
    unfold collectionEnabled
    rw [hsigma, hcutoff, hfreeze]
  rw [hround, hraw, heq, CoordinatorCollectionLedger.localQueueRecord]
  by_cases hf : r.input.time.val + 1 < l0.freezeAt
  · have hc : c.enabled = true := by simpa only [hf, decide_true] using hdate
    simp only [hc, CoordinatorCollectionLedger.sourceRound, hf, decide_true,
      Bool.and_self, ite_true, harrival]
  · have hc : c.enabled = false := by simpa only [hf, decide_false] using hdate
    simp only [hc, Bool.false_and, Bool.false_eq_true, ite_false, hdisabled hc a]

/-- Extraction agrees slot by slot with the same calendar cells. -/
private theorem inputQueueRecords_eq_cells
    (l0 : Ledger rate) (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (D : List (RoundInput p.K)) (hD : D.length = records.length)
    (hcall : ∀ j : Fin records.length, ∃ done : CompletedRound rate,
      extractRound records[j.val] = some done ∧
      ∀ a, CoordinatorCollectionLedger.localQueueRecord l0
        done.input.round done.input.enabled done.input.raw a =
          ((D[j.val]'(by omega)).enabled,
            quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (D[j.val]'(by omega)) a)) :
    ∀ a, CollectionKnownQueueContinuation.inputQueueRecords l0 a (inputs records) =
      D.map (fun c => (c.enabled,
        quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) := by
  induction records generalizing D with
  | nil =>
    have hd : D = [] := List.length_eq_zero_iff.mp (by simpa only [List.length_nil] using hD)
    subst D
    intro a
    rfl
  | cons r records ih =>
    cases D with
    | nil => simp only [List.length_nil, List.length_cons] at hD; omega
    | cons c D =>
      obtain ⟨done, hext, hqueue⟩ := hcall ⟨0, by simp only [List.length_cons]; omega⟩
      simp only [List.getElem_cons_zero] at hext hqueue
      have htail := ih D (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hD)
        (fun j => by
          simpa only [List.getElem_cons_succ] using
            hcall ⟨j.val + 1, by simpa only [List.length_cons] using Nat.succ_lt_succ j.isLt⟩)
      intro a
      simp only [inputs, completed, List.filterMap_cons, hext, List.map_cons,
        CollectionKnownQueueContinuation.inputQueueRecords] at htail ⊢
      rw [hqueue a, htail a]

private theorem calendar_coordinates
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (q : ℕ) (G : List (RoundInput p.K))
    (hlen : G.length = q)
    (hq : q ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + q) z = some G) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let Omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h z
    (∀ k : Fin q,
      let r := R[k.val]'(Nat.lt_of_lt_of_le k.isLt hq)
      let c := G[k.val]'(by omega)
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
      r.input.time.val = s + k.val ∧
      (Omega[k.val]'(by
        simpa only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
          ReferenceCompleteNumericalBranchObservation.branchCalendar, List.length_map, R] using
            (Nat.lt_of_lt_of_le k.isLt hq))).1 = r.input.time ∧
      ((Omega[k.val]'(by
        simpa only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
          ReferenceCompleteNumericalBranchObservation.branchCalendar, List.length_map, R] using
            (Nat.lt_of_lt_of_le k.isLt hq))).2.2).map (Sum.elim id id) =
        some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c)) ∧
    (∀ c ∈ G, c.enabled = false → c.recordedArm = none ∧ ∀ a,
      quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) := by
  intro R s Omega
  change q ≤ R.length at hq
  have hc := prefixInputs_readout rewards C_star C_h z q G hlen hq hprefix
  constructor
  · intro k
    have htimes : R.map (fun r => r.input.time.val) = List.range' s (p.T - s) :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values rate z rewards C_star C_h
    have hlenR : R.length = p.T - s :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
    have hindex : k.val < R.length := Nat.lt_of_lt_of_le k.isLt hq
    have hcal : k.val < (List.range' s (p.T - s)).length := by
      simp only [List.length_range']
      omega
    have ht : (R[k.val]'hindex).input.time.val = s + k.val := by
      have hget : (R.map (fun r => r.input.time.val))[k.val]'(by simpa only [List.length_map] using hindex) =
          (List.range' s (p.T - s))[k.val]'hcal := by simp only [htimes]
      simpa only [List.getElem_map, List.getElem_range', Nat.one_mul] using hget
    refine ⟨hc k, ht, ?_, ?_⟩
    · simp only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
        ReferenceCompleteNumericalBranchObservation.branchCalendar, List.getElem_map, R]
    · simpa only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
        ReferenceCompleteNumericalBranchObservation.branchCalendar, List.getElem_map] using
        tagged_readout_of_cell0 _ _ (hc k)
  · intro c hmem hdisabled
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hmem
    have hkq : k < q := by omega
    exact cell0_disabled _ _ (hc ⟨k, hkq⟩) hdisabled

private theorem source_cell_eq
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (lc rc : Choice rate) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (lv : CoordinatorRecorderComplementBridge.LocalInputsValid
      (collectionRecordingInput left.output.preparation lc.payload lc.started lc.weights))
    (rv : CoordinatorRecorderComplementBridge.LocalInputsValid
      (collectionRecordingInput right.output.preparation rc.payload rc.started rc.weights))
    (he : left = right) (hc : lc = rc) :
    ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate left lc rewards lv =
      ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate right rc rewards rv := by
  cases he
  cases hc
  rfl

/-- A particular initialized-stream witness has the original strict-past cells.
Only proof-irrelevant certificates are identified; the dispatch witnesses are
compared through their actual windows and successful calls. -/
private theorem stream_cells_eq_past
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t)
    (L : List (RoundInput p.K))
    (hL : ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h +
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h hc
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hs).records).length <
          p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (f : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) z rewards C_star C_h
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hc hs hshort)
    (D0 : List (RoundInput p.K)) (hD0 : D0.length = f.stream.ell)
    (hsource : ∀ n : Fin f.stream.ell,
      let r := f.stream.window[n.val]'(lt_of_lt_of_le n.isLt f.stream.withinWindow)
      let c := D0[n.val]'(by omega)
      ∃ (call : Choice rate) (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (collectionRecordingInput r.output.preparation call.payload call.started call.weights)),
        choice r.input = some call ∧
        c = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate r call rewards valid)
    (hell : f.stream.ell = (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length).length) :
    ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z rewards C_star C_h hc
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hs ++ D0 = L := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let count := p.T - s
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  obtain ⟨hc', hs', hshort', f', head', valid', D', L', _hsu, _hut, _hu, hdate,
    _hp, _hlast, hhead', hDlen', hDzero', hDread', hLdef', hL', _hLlen', _hcoverage⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage rate rewards C_star C_h u t z hz.1
  have hLeq : L' = L := Option.some.inj (hL'.symm.trans hL)
  have hwindow : f.stream.window = f'.stream.window :=
    f.stream.windowIsActual.trans f'.stream.windowIsActual.symm
  have hbirth := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
    rate rewards C_star C_h u t z hz
  change s + (w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length) = t.val at hbirth
  change s + w + f'.stream.ell = t.val at hdate
  change f.stream.ell = (ReferenceCollectionPhaseHistory.collectionWindow R w).length at hell
  have hell' : f.stream.ell = f'.stream.ell := by omega
  obtain ⟨head, _initializer, valid, D, hhead, _hpay, _hinit, _hchecked,
    hDlen, hDzero, hcells⟩ :=
    ReferenceFirstCollectionAllArmNumericalStream.stream_source_prefix rate z rewards C_star C_h
      hc count hs hshort f.stream
  have hD0eq : D0 = D := by
    apply List.ext_getElem
    · exact hD0.trans hDlen.symm
    · intro n hn hn'
      have hnell : n < f.stream.ell := by omega
      obtain ⟨call0, valid0, hcall0, heq0⟩ := hsource ⟨n, hnell⟩
      obtain ⟨call, validCall, hcall, _hpay, heq, _⟩ := hcells ⟨n, hnell⟩
      have heqcall : call0 = call := Option.some.inj (hcall0.symm.trans hcall)
      exact heq0.trans ((source_cell_eq _ _ call0 call rewards valid0 validCall rfl heqcall).trans heq.symm)
  have hcut : f.stream.cutoff.cut = f'.stream.cutoff.cut := by
    calc
      _ = f.stream.window[0]'(by have h := f.stream.windowNonempty; omega) := f.stream.cutoffIsHead.symm
      _ = f'.stream.window[0]'(by have h := f'.stream.windowNonempty; omega) := List.getElem_of_eq hwindow _
      _ = _ := f'.stream.cutoffIsHead
  have hheadAt : choice f'.stream.cutoff.cut.input = some head := by rw [← hcut]; exact hhead
  have heqhead : head = head' := Option.some.inj (hheadAt.symm.trans hhead')
  have hDeq : D = D' := by
    apply List.ext_getElem
    · exact hDlen.trans (hell'.trans hDlen'.symm)
    · intro n hn hn'
      have hnell : n < f.stream.ell := by omega
      have hnell' : n < f'.stream.ell := by omega
      by_cases hnzero : n = 0
      · subst n
        have hzero' := (List.getElem?_eq_some_iff.mp hDzero').2
        exact hDzero.trans ((source_cell_eq _ _ head head' rewards valid valid' hcut heqhead).trans hzero'.symm)
      · obtain ⟨_call, _validCall, _hcall, _hpay, _heq, _hrows, _hJ, _hrewards,
          _htime, _henabled, _hreward, _hrate, _hphysical, hread⟩ := hcells ⟨n, hnell⟩
        have hread0 := collection_readout_zero s _ _ (hread (Nat.pos_of_ne_zero hnzero))
        have hread' := hDread' ⟨n, hnell'⟩
        have hrecord : (f.stream.window[n]'(lt_of_lt_of_le hnell f.stream.withinWindow)) =
            (f'.stream.window[n]'(lt_of_lt_of_le hnell' f'.stream.withinWindow)) :=
          List.getElem_of_eq hwindow _
        rw [hrecord] at hread0
        rw [List.getElem?_eq_getElem hn'] at hread'
        exact Option.some.inj (hread0.symm.trans hread')
  rw [hD0eq, hDeq]
  exact hLdef'.symm.trans hLeq

/-- The particular assigned LIVE cells are the same chronological cells as
the original prefix, including the birth cell. -/
private theorem assigned_live_cells_eq
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (b e : ℕ)
    (L B : List (RoundInput p.K)) (c : RoundInput p.K)
    (hL : L.length = b) (hlen : ((L ++ [c]) ++ B).length = e)
    (he : e ≤ (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (hprefix : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e) z = some ((L ++ [c]) ++ B))
    (P : Payload rate)
    (hlater : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < P.sigma.val)
    (N : ℕ) (hN : N = e - b)
    (hw : (((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).drop b).take N).length = N)
    (v : ∀ n : Fin N, Selection
      ((((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).drop b).take N)[n.val]'(by omega)).input)
    (ho : ∀ n : Fin N, ReferenceLaterLiveNumericalReadout.preparedOrdinary
      ((((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).drop b).take N)[n.val]'(by omega)))
    (hv : ∀ n : Fin N,
      let r := (((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).drop b).take N)[n.val]'(by omega)
      r.output.preparation.coordinator.selection = some (v n) ∧
      (v n).view.payload = P ∧ (v n).view.cutoff = none ∧
      CoordinatorLocalArmChoice.assignmentIsLive (v n).view.payload (v n).view.cutoff r.input.time) :
    let Cells : Fin N → RoundInput p.K := fun n =>
      ReferenceFirstWindowNumericalStream.sourceCell
        ((((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).drop b).take N)[n.val]'(by omega))
        (v n).view.payload (v n).view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates _ (ho n))
        (v n).view.complementWeights (v n).view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v n))
    List.ofFn Cells = [c] ++ B := by
  intro Cells
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let A := (L ++ [c]) ++ B
  change A.length = e at hlen
  change e ≤ R.length at he
  change ((R.drop b).take N).length = N at hw
  have hbe : b < e := by
    have hAlen := hlen
    simp only [A, List.length_append, List.length_singleton] at hAlen
    omega
  have hAread := prefixInputs_readout rewards C_star C_h z e A hlen he hprefix
  have hCells : ∀ n : Fin N,
      Cells n = A[b + n.val]'(by have hn := n.isLt; omega) := by
    intro n
    let r := ((R.drop b).take N)[n.val]'(by omega)
    obtain ⟨hselected, hpay, _hcut, hlive⟩ := hv n
    change r.output.preparation.coordinator.selection = some (v n) at hselected
    change CoordinatorLocalArmChoice.assignmentIsLive (v n).view.payload (v n).view.cutoff r.input.time at hlive
    have hbase : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
        (v n).view.payload.sigma.val := by rw [hpay]; exact hlater
    have hor : ReferenceLaterLiveNumericalReadout.preparedOrdinary r := ho n
    have hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r = some (Cells n) := by
      unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
      simp only [hselected, hbase, hlive, and_self, ite_true, dite_eq_left hor]
      rfl
    have hcell := cell0_of_live _ r (Cells n) hread
    have hnR : b + n.val < R.length := by have hn := n.isLt; omega
    have hr : r = R[b + n.val]'hnR := by
      simp only [r, List.getElem_take, List.getElem_drop]
    rw [hr] at hcell
    exact Option.some.inj (hcell.symm.trans (hAread ⟨b + n.val, by have hn := n.isLt; omega⟩))
  have heq : List.ofFn Cells = A.drop b := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_drop]
      exact hN.trans (congrArg (fun k => k - b) hlen).symm
    · intro n hn hn'
      simp only [List.getElem_ofFn, List.getElem_drop]
      exact hCells ⟨n, by simpa only [List.length_ofFn] using hn⟩
  rw [heq]
  change ((L ++ [c]) ++ B).drop b = [c] ++ B
  rw [List.append_assoc, ← hL, List.drop_append_length]

private theorem window_eq_birth_cons
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (b : ℕ)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hb : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b]? = some birth)
    (hk : b + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix rate rewards C_star C_h z (b + 1)
    (R.drop b).take (1 + W.length) = birth :: W := by
  intro R W
  have he := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_length_le rewards C_star C_h z ⟨b + 1, hk⟩
  change b + 1 + W.length ≤ R.length at he
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_cons]
    omega
  · intro n hn hn'
    cases n with
    | zero =>
      simp only [List.getElem_take, List.getElem_drop, Nat.add_zero, List.getElem_cons_zero]
      exact (List.getElem?_eq_some_iff.mp hb).2
    | succ n =>
      have hnW : n < W.length := by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hn'
      simp only [List.getElem_take, List.getElem_drop, List.getElem_cons_succ]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index rewards C_star C_h z
          ⟨b + 1, hk⟩ n hnW).symm

private theorem unstopped_word_eq_raw (cells : List (RoundInput p.K))
    (hdisabled : ∀ c ∈ cells, c.enabled = false → ∀ a,
      quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0)
    (a : Fin p.K) :
    cells.map (fun c => UnstoppedRecordedQueueComparison.unstoppedRecord
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) =
    cells.map (fun c => (c.enabled,
      quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) := by
  apply List.map_congr_left
  intro c hc
  cases he : c.enabled with
  | false =>
    simp only [UnstoppedRecordedQueueComparison.unstoppedRecord, he,
      Bool.false_eq_true, ite_false, hdisabled c hc he a]
  | true =>
    simp only [UnstoppedRecordedQueueComparison.unstoppedRecord, he, ite_true]

/-- Project F onto its exact segment while preserving its original armwise
words and initialization witnesses. All localizers are checked equalities of
the original producer's optional values. -/
private theorem firstCell_segment_replay_values
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    ∀ (L : List (RoundInput p.K)) (c : RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L →
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c →
      R[b]? = some birth →
    ∀ (rout : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (qout : CoordinatorLiveServiceFinish.OwnedRegisters rout) (beta : Fin (p.m - 1) → ℕ),
      birth.output.next.coordinator = .live rout qout beta →
      t.val + 1 < p.T →
    ∀ (hk : b + 1 < R.length)
      (hstate : R[b + 1].input.state.coordinator = .live rout qout beta)
      (hlater : s < rout.payload.sigma.val),
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix rate rewards C_star C_h z (b + 1)
    let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
      rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
    let e := b + 1 + W.length
    let A := (L ++ [c]) ++ B
    ∀ (_he : e < R.length) (seg : Segment rate) (I : Initializer p),
      segmentAt R e = some seg → seg.context.initializer = some I →
    let l0 := seg.context.preLedger
    (seg.final.pending = ∅ → ∀ a : Fin p.K,
            (∃ j : CanonicalFastSampling.FastArm rout.payload.slowSet, j.val = a ∧
              let Qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
              let E := A.map (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord Qp cell a)
              let Eprev := (A.take (A.length - 1)).map
                (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord Qp cell a)
              let H := CollectionKnownQueueContinuation.inputQueueRecords l0 a seg.inputs
              let V := QueueReplay.replay (4 * rate.n) (0, 0) E
              let Vprev := QueueReplay.replay (4 * rate.n) (0, 0) Eprev
              let Q := QueueReplay.replay (4 * rate.n) (0, 0) (E ++ H)
              let last := CollectionKnownQueueContinuation.replayLastService
                (4 * rate.n) (0, V.2) (V.1 - Vprev.1) H
              seg.final.cutoffRegisters a =
                some (CoordinatorCollectionLedger.CutoffRegister.mk V.1 V.2 (V.1 - Vprev.1)) ∧
              seg.final.currentRegisters a = some (CoordinatorCollectionLedger.CurrentRegister.mk Q.2 last) ∧
              V.1 + seg.final.increment a = Q.1 ∧
              H.length = seg.inputs.length ∧ H.length = seg.records.length ∧ 0 < H.length ∧
              last = (QueueReplay.replay (4 * rate.n) (0, V.2) H).1 -
                (QueueReplay.replay (4 * rate.n) (0, V.2) (H.take (H.length - 1))).1) ∨
            (∃ i : Fin (p.m - 1), rout.payload.assignment.assigned i = a ∧
              ∃ (k : Fin R.length) (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
              e ≤ k.val ∧ k.val < e + seg.records.length ∧ R[k.val] ∈ seg.records ∧
              ReferenceCollectionPhaseHistory.AcceptedUp R[k.val].input i U ∧
              U.val.sigma = seg.final.sigma ∧
              ∃ c : Choice rate, choice R[k.val].input = some c ∧ c.payload = seg.context.payload ∧
              c.payload.assignment.assigned i = a ∧
              ∃ IA : Initializer p, seg.context.initializer = some IA ∧
                IA = I ∧ IA.checkedStart rate = CoordinatorCollectionLedger.Checked.success seg.context.preLedger ∧
              let P := c.payload
              let a := P.assignment.assigned i
              let sigma := P.sigma.val + 1
              let uc := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)))
              let N := uc - sigma
              let L := (R.drop b).take N
              N = e - b ∧
              L.map (fun (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) => r.input.time.val + 1) =
                List.range' sigma N ∧
              ∃ (hLlen : L.length = N)
                (v : ∀ n : Fin N, Selection (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input)
                (ho : ∀ n : Fin N, ReferenceLaterLiveNumericalReadout.preparedOrdinary
                  (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm))),
                (∀ n : Fin N, (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).output.preparation.coordinator.selection =
                  some (v n) ∧ (v n).view.payload = P ∧ (v n).view.cutoff = none ∧
                  CoordinatorLocalArmChoice.assignmentIsLive (v n).view.payload (v n).view.cutoff
                    (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input.time) ∧
              (∀ (n : Fin N) (f : Fin (p.m - 1)), (ReferenceFollowerFixedReply.actualChoice
                  (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) f).configuration =
                DeclaredFollowerLocalRound.LocalConfiguration.ordinary
                  (ReferenceLaterLiveNumericalReadout.preparedStates
                    (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n) f)
                  (ReferenceLaterLiveNumericalReadout.preparedMemories
                    (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n) f)) ∧
              let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun n =>
                ReferenceFirstWindowNumericalStream.sourceCell
                  (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (v n).view.payload
                  (v n).view.pendingAtChoice
                  (ReferenceLaterLiveNumericalReadout.preparedStates
                    (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n))
                  (v n).view.complementWeights (v n).view.cutoff
                  (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v n))
              let A := List.ofFn (fun n => ((Cells n).enabled,
                RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) (Cells n) a))
              ∃ hc : (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true,
              ∃ hs : ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h + (p.T - s) ≤ p.T,
              ∃ hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                  z rewards C_star C_h hc (p.T - s) hs).records).length < p.T - s,
              ∃ f : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
                (rate := rate) z rewards C_star C_h (p.T - s) hc hs hshort,
              ∃ (head0 : Choice rate) (_valid0 : CoordinatorRecorderComplementBridge.LocalInputsValid
                (collectionRecordingInput f.stream.cutoff.cut.output.preparation head0.payload head0.started head0.weights))
                (D0 : List (RecordedQueueRun.RoundInput p.K)),
                choice f.stream.cutoff.cut.input = some head0 ∧ head0.payload = f.stream.payload ∧
                ∃ hDlen : D0.length = f.stream.ell,
                (∀ n : Fin f.stream.ell,
                  let r := f.stream.window[n.val]'(lt_of_lt_of_le n.isLt f.stream.withinWindow)
                  let cell := D0[n.val]'(by rw [hDlen]; exact n.isLt)
                  ∃ (call : Choice rate) (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
                    (collectionRecordingInput r.output.preparation call.payload call.started call.weights)),
                    choice r.input = some call ∧ call.payload = f.stream.payload ∧
                    cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate r call rewards validCall ∧
                    r.input.rows = z.1.2 ∧ r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
                    r.input.rewards = rewards ∧
                    r.input.time.val = ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h +
                      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                          z rewards C_star C_h hc (p.T - s) hs).records).length + n.val) ∧
                f.stream.ell = (ReferenceCollectionPhaseHistory.collectionWindow R
                  (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length ∧
              let Cells0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
                rate z rewards C_star C_h hc (p.T - s) hs
              let E0 := ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0)
              let E := E0 ++ A
              let H := seg.records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a)
              let V := QueueReplay.replay (4 * rate.n) (0, 0) E
              let Vprev := QueueReplay.replay (4 * rate.n) (0, 0) (E0 ++ A.take (N - 1))
              let Q := QueueReplay.replay (4 * rate.n) (0, 0) (E ++ H)
              let Qprev := QueueReplay.replay (4 * rate.n) (0, 0)
                (E ++ (seg.records.take (seg.records.length - 1)).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a))
              seg.final.cutoffRegisters a =
                some (CoordinatorCollectionLedger.CutoffRegister.mk V.1 V.2 (V.1 - Vprev.1)) ∧
              seg.final.currentRegisters a =
                some (CoordinatorCollectionLedger.CurrentRegister.mk Q.2 (Q.1 - Qprev.1)) ∧
              V.1 + seg.final.increment a = Q.1)) := by
  classical
  intro R s b L c birth hL hc hb rout qout beta hlive htT hk hstate hlater W B e A he seg I hseg hI l0
  obtain ⟨L', c', birth', hL', hc', _hprefix, _hLb, _hbsub, _htime, _henabled,
    hb', _har, _ht, _hrows, _hJ, _hrewards, _hcurrent, _hnext, _hmode, hcont⟩ :=
    ReferenceFirstCorrectedAllArmSegmentFinalNumericalJoin.firstCell_all_arm_segment_final_numerical_values
      rate rewards C_star C_h u t z hz
  clear _hcurrent _hnext
  have hLeq : L' = L := Option.some.inj (hL'.symm.trans hL)
  have hceq : c' = c := Option.some.inj (hc'.symm.trans hc)
  have hbeq : birth' = birth := Option.some.inj (hb'.symm.trans hb)
  subst L'
  subst c'
  subst birth'
  obtain ⟨_hsigma, _harms, hcont⟩ := hcont rout qout beta hlive
  obtain ⟨_next, _hk, _hstate, _hlater, _hnextIndex, _hnextState,
    _hBlen, _heR, _heT, _hWtimes, _hprefixA, _hAlen, _hAdate,
    _rE, _qE, _hp, _hlastW, _hstateE, hboundary⟩ := hcont htT
  clear hcont _harms
  rcases hboundary with hhor | ⟨_he, chosen, _hchosen, _hprepared, hbranch⟩
  · change e = R.length at hhor
    exact False.elim ((Nat.ne_of_lt he) hhor)
  · cases chosen <;> try contradiction
    next dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected =>
      obtain ⟨_htau, _hscan, segF, IF, hsegF, _hentry, _hpay, hpre, hIF,
        _hIdef, _hchecked, _harm, _hIsigma, _hIcut, _hfreeze, _hbase, _hnonempty,
        _hpartition, _hexit, _hrun, _hcalendar, _hcount, _hpositive, _hwhole,
        _hpayAll, _hduring, _ccut, _hcell, _hprefixCut, _saved, _hend, _hcursor,
        _hle, _hwitnesses, _hboundary, hnum⟩ := hbranch
      have hsegEq : segF = seg := Option.some.inj (hsegF.symm.trans hseg)
      subst segF
      have hIEq : IF = I := Option.some.inj (hIF.symm.trans hI)
      cases hIEq
      rw [← hpre] at hnum
      intro hempty a
      rcases hnum hempty a with hj | hi
      · exact Or.inl hj
      · exact Or.inr hi

private theorem replay_add_score (capacity score backlog : ℕ) (records : List (Bool × ℕ)) :
    QueueReplay.replay capacity (score, backlog) records =
      (score + (QueueReplay.replay capacity (0, backlog) records).1,
        (QueueReplay.replay capacity (0, backlog) records).2) := by
  induction records generalizing score backlog with
  | nil => rfl
  | cons record rest ih =>
      change QueueReplay.replay capacity (QueueReplay.transition capacity (score, backlog) record) rest =
        (score + (QueueReplay.replay capacity
          (QueueReplay.transition capacity (0, backlog) record) rest).1,
          (QueueReplay.replay capacity (QueueReplay.transition capacity (0, backlog) record) rest).2)
      rw [CollectionKnownQueueContinuation.queueReplay_transition_add_score]
      rw [ih (score + (QueueReplay.transition capacity (0, backlog) record).1)
        (QueueReplay.transition capacity (0, backlog) record).2]
      rw [ih (QueueReplay.transition capacity (0, backlog) record).1
        (QueueReplay.transition capacity (0, backlog) record).2]
      simp only [Nat.add_assoc]

private theorem take_before_last_append {α : Type*} (A D : List α) (hD : D ≠ []) :
    (A ++ D).take ((A ++ D).length - 1) = A ++ D.take (D.length - 1) := by
  have hpos := List.length_pos_iff.mpr hD
  have hindex : (A ++ D).length - 1 = A.length + (D.length - 1) := by
    simp only [List.length_append]
    omega
  rw [hindex, List.take_append,
    List.take_of_length_le (show A.length ≤ A.length + (D.length - 1) by omega),
    Nat.add_sub_cancel_left]

private theorem replay_tail_difference (cap : ℕ) (E H : List (Bool × ℕ)) :
    let V := QueueReplay.replay cap (0, 0) E
    (QueueReplay.replay cap (0, V.2) H).1 -
      (QueueReplay.replay cap (0, V.2) (H.take (H.length - 1))).1 =
    (QueueReplay.replay cap (0, 0) (E ++ H)).1 -
      (QueueReplay.replay cap (0, 0) (E ++ H.take (H.length - 1))).1 := by
  intro V
  rw [QueueReplay.replay_append, QueueReplay.replay_append]
  change _ = (QueueReplay.replay cap (V.1, V.2) H).1 -
    (QueueReplay.replay cap (V.1, V.2) (H.take (H.length - 1))).1
  rw [replay_add_score cap V.1 V.2 H,
    replay_add_score cap V.1 V.2 (H.take (H.length - 1))]
  simp only [Nat.add_sub_add_left]

/-- One original dated calendar through the actual first corrected collection
endpoint. Outside and assigned words, including their previous cuts, are
identified literally with this same calendar. Endpoint numerical equations
remain conditional on the final ledger's local empty-pending test. -/
theorem firstCell_collection_calendar_numerical_values
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let b := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex rate rewards C_star C_h z
    let Omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate rewards C_star C_h z
    ∃ (L : List (RoundInput p.K)) (c : RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ s + b = t.val ∧ R[b]? = some birth ∧
      birth.input.time = t ∧ birth.input.rows = z.1.2 ∧
      birth.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      birth.input.rewards = rewards ∧ c.enabled = true ∧
      ReferenceLaterLiveNumericalReadout.laterLiveReadout s birth = some c ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate birth = some c ∧
      (birth.output.next.coordinator = .dagger ∨
        ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ),
          birth.output.next.coordinator = .live r q base) ∧
      ∀ (rout : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qout : CoordinatorLiveServiceFinish.OwnedRegisters rout) (beta : Fin (p.m - 1) → ℕ),
        birth.output.next.coordinator = .live rout qout beta →
        rout.payload.sigma = t ∧
      ∀ _hq : t.val + 1 < p.T,
      ∃ (hk : b + 1 < R.length)
        (hstate : R[b + 1].input.state.coordinator = .live rout qout beta)
        (hlater : s < rout.payload.sigma.val),
      let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix rate rewards C_star C_h z (b + 1)
      let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
        rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
      let e := b + 1 + W.length
      let A := (L ++ [c]) ++ B
      ∃ hB : B.length = W.length,
        e ≤ R.length ∧ t.val + 1 + W.length ≤ p.T ∧ A.length = e ∧
        s + e = t.val + 1 + W.length ∧
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s + e) z = some A ∧
        (R.drop b).take (1 + W.length) = birth :: W ∧
        (∀ j : Fin W.length,
          (W[j.val]).input.time.val = t.val + 1 + j.val ∧
          ReferenceLaterLiveNumericalReadout.laterLiveReadout s W[j.val] =
            some (B[j.val]'(by omega)) ∧
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate W[j.val] =
            some (B[j.val]'(by omega))) ∧
      ∃ (rE : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (qE : CoordinatorLiveServiceFinish.OwnedRegisters rE),
        rE.payload = rout.payload ∧
        (∀ he : e < R.length, R[e].input.state.coordinator = .live rE qE beta) ∧
        (e = R.length ∨
        ∃ (he : e < R.length) (seg : Segment rate) (I : Initializer p) (l0 : Ledger rate),
          segmentAt R e = some seg ∧ seg.entry = R[e] ∧
          seg.context.payload = rout.payload ∧ seg.context.preLedger = l0 ∧
          seg.context.initializer = some I ∧
          I = cutoffInitializer (liveRegistersAt rE R[e].input.time)
            (liveOwnedAt rE qE R[e].input.time) beta R[e].input.time ∧
          I.checkedStart rate = .success l0 ∧
          I.assignment.arm = rout.payload.assignment.assigned ∧
          I.sigma = t.val + 1 ∧ I.cutoff = s + e + 1 ∧
          I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val rout.payload.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧
          I.freezeAt = rE.gridBoundary ∧ I.base = beta ∧
          ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
          (∃ during, seg.records = seg.entry :: during) ∧
          seg.records ++ seg.remaining = R.drop e ∧
        ∃ (D : List (RoundInput p.K)) (hD : D.length = seg.records.length),
          (∀ j : Fin seg.records.length,
            let r := seg.records[j.val]
            let c := D[j.val]'(by omega)
            ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
            ∃ done : CompletedRound rate,
              extractRound r = some done ∧ preparedFollowersUnoccupied r ∧
              laterCollectionReadout s r = some c ∧
              done.context.payload = rout.payload ∧
              done.context.preLedger.sigma = l0.sigma ∧
              done.context.preLedger.cutoff = l0.cutoff ∧
              done.context.preLedger.freezeAt = l0.freezeAt ∧
              c.enabled = collectionEnabled l0 r.input.time ∧
              c.enabled = decide (r.input.time.val + 1 < l0.freezeAt) ∧
              c.rate = rout.payload.rate ∧
              c.reward = (fun a => ((rewards r.input.time a).val : ℝ) / (ConstructorDimensions.D p : ℝ)) ∧
              r.input.rows = z.1.2 ∧
              r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
              r.input.rewards = rewards ∧
              ∃ out : CoordinatorRecordingOperation.Output p,
                laterCollectionCall s r =
                  some ⟨done.context.payload, done.context.preLedger, done.context.started, done.context.weights⟩ ∧
                CoordinatorRecorderComplementBridge.run (collectionRecordingInput r.output.preparation
                  done.context.payload done.context.started done.context.weights) = some out ∧
                r.output.coordinator.recording = some out ∧ out.gateArm = c.recordedArm ∧
                rawDiagnostic r = out.gateArm.map (fun a => (a, out.rawArrival)) ∧
                (∀ a, CoordinatorCollectionLedger.localArrival (rawDiagnostic r) a =
                  RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
                (∀ a, physicalQueueRecord l0 a r = (c.enabled,
                  if r.input.time.val + 1 < l0.freezeAt then
                    RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a else 0)) ∧
                (c.enabled = false → c.recordedArm = none ∧ ∀ a,
                  RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
                (∀ a, physicalQueueRecord l0 a r = (c.enabled,
                  RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))) ∧
          (∀ a,
            CollectionKnownQueueContinuation.inputQueueRecords l0 a seg.inputs =
              D.map (fun cell => (cell.enabled,
                quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
            seg.records.map (physicalQueueRecord l0 a) =
              D.map (fun cell => (cell.enabled,
                quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
            ∀ h, (seg.records.take h).map (physicalQueueRecord l0 a) =
              (D.take h).map (fun cell => (cell.enabled,
                quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))) ∧
          let q := e + seg.records.length
          let G := A ++ D
          ∃ (hG : G.length = q) (hq : q ≤ R.length),
            s + q ≤ p.T ∧ R.take q = R.take e ++ seg.records ∧
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
              rate rewards C_star C_h (s + q) z = some G ∧
          (∀ k : Fin q,
            let r := R[k.val]'(Nat.lt_of_lt_of_le k.isLt hq)
            let c := G[k.val]'(by omega)
            ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
            r.input.time.val = s + k.val ∧
            (Omega[k.val]'(by
              simpa only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
                ReferenceCompleteNumericalBranchObservation.branchCalendar, List.length_map, R] using
                  (Nat.lt_of_lt_of_le k.isLt hq))).1 = r.input.time ∧
            ((Omega[k.val]'(by
              simpa only [Omega, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
                ReferenceCompleteNumericalBranchObservation.branchCalendar, List.length_map, R] using
                  (Nat.lt_of_lt_of_le k.isLt hq))).2.2).map (Sum.elim id id) =
              some (ReferenceCompleteNumericalBranchObservation.encodeNumerical c)) ∧
          (∀ c ∈ G, c.enabled = false → c.recordedArm = none ∧ ∀ a,
            quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) ∧
          (∀ a,
            A.map (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a) =
              A.map (fun cell => (cell.enabled,
                quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
            (A.take (e - 1)).map (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a) =
              (A.take (e - 1)).map (fun cell => (cell.enabled,
                quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
            ∀ h, (G.take h).map (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a) =
              (G.take h).map (fun cell => (cell.enabled,
                quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))) ∧
          (let raw := fun (a : Fin p.K) (C : List (RoundInput p.K)) =>
            C.map (fun cell => (cell.enabled,
              quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))
           let U := fun (a : Fin p.K) (h : ℕ) => QueueReplay.replay (4 * rate.n) (0, 0) (raw a (G.take h))
           seg.final.pending = ∅ → ∀ a,
             seg.final.cutoffRegisters a = some ⟨(U a e).1, (U a e).2, (U a e).1 - (U a (e - 1)).1⟩ ∧
             seg.final.currentRegisters a = some ⟨(U a q).2, (U a q).1 - (U a (q - 1)).1⟩ ∧
             (U a e).1 + seg.final.increment a = (U a q).1 ∧
             ((∃ j : CanonicalFastSampling.FastArm rout.payload.slowSet, j.val = a ∧
                 A.map (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord
                   (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a) = raw a A ∧
                 (A.take (e - 1)).map (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord
                   (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a) = raw a (A.take (e - 1)) ∧
                 CollectionKnownQueueContinuation.inputQueueRecords l0 a seg.inputs = raw a D) ∨
               ∃ i : Fin (p.m - 1), rout.payload.assignment.assigned i = a ∧
               ∃ (k : Fin R.length) (up : ReferenceCollectionPhaseHistory.UpRecord p rate),
                 e ≤ k.val ∧ k.val < q ∧ R[k.val] ∈ seg.records ∧
                 ReferenceCollectionPhaseHistory.AcceptedUp R[k.val].input i up ∧ up.val.sigma = seg.final.sigma ∧
               ∃ cA : Choice rate, choice R[k.val].input = some cA ∧
                 cA.payload = seg.context.payload ∧ cA.payload.assignment.assigned i = a ∧
               ∃ IA : Initializer p, seg.context.initializer = some IA ∧ IA = I ∧
                 IA.checkedStart rate = .success seg.context.preLedger ∧
               let P := cA.payload
               let N := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                 (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                   (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) - (P.sigma.val + 1)
               let window := (R.drop b).take N;
                 P = rout.payload ∧ N = 1 + W.length ∧ window = birth :: W ∧
               ∃ (hw : window.length = N) (Cells : Fin N → RoundInput p.K),
                 (∀ n : Fin N,
                   ReferenceLaterLiveNumericalReadout.laterLiveReadout s
                     (window[n.val]'(Nat.lt_of_lt_of_eq n.isLt hw.symm)) = some (Cells n) ∧
                   ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
                     (window[n.val]'(Nat.lt_of_lt_of_eq n.isLt hw.symm)) = some (Cells n)) ∧
                 List.ofFn Cells = [c] ++ B ∧
               ∃ hc0 : (ReferenceInitializationRun.output
                 (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true,
               ∃ hs0 : ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h + (p.T - s) ≤ p.T,
               ∃ hshort0 : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                 (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                   z rewards C_star C_h hc0 (p.T - s) hs0).records).length < p.T - s,
               ∃ f : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
                 (rate := rate) z rewards C_star C_h (p.T - s) hc0 hs0 hshort0,
               ∃ (D0 : List (RoundInput p.K)) (hD0 : D0.length = f.stream.ell),
                 (∀ n : Fin f.stream.ell,
                   let r := f.stream.window[n.val]'(lt_of_lt_of_le n.isLt f.stream.withinWindow)
                   ∃ (call : Choice rate) (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
                     (collectionRecordingInput r.output.preparation call.payload call.started call.weights)),
                     choice r.input = some call ∧ (D0[n.val]'(Nat.lt_of_lt_of_eq n.isLt hD0.symm)) =
                       ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate r call rewards valid) ∧
               let Cells0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
                 rate z rewards C_star C_h hc0 (p.T - s) hs0
               let E0 := ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0)
               let Ai := List.ofFn (fun n => ((Cells n).enabled,
                 quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) (Cells n) a));
                 Cells0 ++ D0 = L ∧ E0 = raw a L ∧ Ai = raw a ([c] ++ B) ∧ E0 ++ Ai = raw a A ∧
                 E0 ++ Ai.take (N - 1) = raw a (A.take (e - 1)) ∧
                 seg.records.map (physicalQueueRecord l0 a) = raw a D ∧
                 (seg.records.take (seg.records.length - 1)).map (physicalQueueRecord l0 a) =
                   raw a (D.take (D.length - 1)))) ∧
          ∃ saved, (endpointState seg.entry.input.state seg.records).coordinator =
            .collection seg.context.payload seg.final saved ∧
            seg.final.cursor = s + q + 1 ∧
            (q = R.length ∨ ∃ hv : q < R.length,
              R[q].input.state = endpointState seg.entry.input.state seg.records ∧
              R[q].input.state.coordinator = .collection seg.context.payload seg.final saved ∧
              R[q].input.time.val = s + q ∧ R.drop q = seg.remaining ∧
              (ReferenceCollectionPhaseHistory.laterChosen R[q].input = false ∨
                ReferenceCollectionPhaseHistory.laterChosen R[q].input = true ∧
                seg.final.pending = ∅ ∧ ∀ i : Fin (p.m - 1),
                  ∃ (k : Fin R.length) (U : ReferenceCollectionPhaseHistory.UpRecord p rate),
                    e ≤ k.val ∧ k.val < q ∧ R[k.val] ∈ seg.records ∧
                    ReferenceCollectionPhaseHistory.AcceptedUp R[k.val].input i U ∧
                    U.val.sigma = seg.final.sigma))) := by
  classical
  intro R s b Omega
  obtain ⟨L, c, birth, hL, hc, hprefix, hLb, _hbsub, htime, _henabled,
    hb, har, ht, _hrows, _hselected, _hrewards, _hcurrent, _hnext, hmode, hcont⟩ :=
    ReferenceFirstCorrectedAllArmSegmentFinalNumericalJoin.firstCell_all_arm_segment_final_numerical_values
      rate rewards C_star C_h u t z hz
  clear _hcurrent _hnext
  have hbirth : ReferenceLaterLiveNumericalReadout.laterLiveReadout s birth = some c := by
    simpa only [ReferenceFirstCollectionCurrentNumericalCell.currentCell, har, Option.bind_some] using hc
  refine ⟨L, c, birth, hL, hc, hprefix, hLb, htime, hb, ht, _hrows, _hselected, _hrewards, _henabled, hbirth,
    cell0_of_live s birth c hbirth, hmode, ?_⟩
  intro rout qout beta hlive
  obtain ⟨hsigma, _harms, hcont⟩ := hcont rout qout beta hlive
  refine ⟨hsigma, ?_⟩
  intro htT
  obtain ⟨_next, hk, hstate, hlater, _hnextIndex, _hnextState,
    hBlen, heR, heT, hWtimes, hprefixA, hAlen, hAdate,
    rE, qE, hp, _hlastW, hstateE, _hboundaryF⟩ := hcont htT
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix rate rewards C_star C_h z (b + 1)
  let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
    rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
  let e := b + 1 + W.length
  let A := (L ++ [c]) ++ B
  clear _hboundaryF _harms hcont
  change A.length = e at hAlen
  change s + e = t.val + 1 + W.length at hAdate
  change B.length = W.length at hBlen
  change W.map (fun r => r.input.time.val) = List.range' (t.val + 1) W.length at hWtimes
  have hprefixA' : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h (s + e) z = some A := by rw [hAdate]; exact hprefixA
  refine ⟨hk, hstate, hlater, hBlen, heR, heT, hAlen, hAdate, hprefixA',
    window_eq_birth_cons rewards C_star C_h z b birth hb hk, ?_, rE, qE, hp, hstateE, ?_⟩
  · intro j
    have hread := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells_readout
      rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater j
    have hget : (W.map (fun r => r.input.time.val))[j.val]'(by simpa only [List.length_map] using j.isLt) =
        (List.range' (t.val + 1) W.length)[j.val]'(by simpa only [List.length_range'] using j.isLt) := by
      simp only [hWtimes]
    have hdate : W[j.val].input.time.val = t.val + 1 + j.val := by
      simpa only [List.getElem_map, List.getElem_range', Nat.one_mul] using hget
    exact ⟨hdate, hread, cell0_of_live s _ _ hread⟩
  · obtain ⟨birthR, routR, qoutR, betaR, hbR, _hdateR, _htR, _hrowsR, _hJR, _hrewardsR,
        _hbornR, _hsigmaR, _hlaterR, hliveR, hcontR⟩ :=
      ReferenceFirstCorrectedReplacementCollectionReadout.firstCell_collection_readout_cover
        rate rewards C_star C_h u t z hz
    have hbirthR : birthR = birth := Option.some.inj (hbR.symm.trans hb)
    subst birthR
    have hroutR : routR = rout := (CoordinatorConfiguration.live.inj (hliveR.symm.trans hlive)).1
    obtain ⟨_heR, _heT, rER, qER, _hpR, hstateER, hboundaryR⟩ := hcontR htT
    rcases hboundaryR with hhor | ⟨he, seg, I, l0, hseg, hentry, hpay, hpre, hI,
      hIdef, hchecked, harm, hIsigma, hIcut, hIscan, hfreeze, hbase, hcut, hnonempty,
      hpartition, _hcalendar, hcover⟩
    · exact Or.inl hhor
    · have hfields := CoordinatorConfiguration.live.inj ((hstateER he).symm.trans (hstateE he))
      have hrER : rER = rE := hfields.1
      have hqER := hfields.2.1
      have hbetaR := hfields.2.2
      subst rER
      cases hqER
      rw [hbetaR] at hIdef hbase
      have hpay' : seg.context.payload = rout.payload := by rw [hpay, hroutR]
      have harm' : I.assignment.arm = rout.payload.assignment.assigned := by rw [harm, hroutR]
      have hIscan' : I.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val rout.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) := by rw [hIscan, hroutR]
      refine Or.inr ⟨he, seg, I, l0, hseg, hentry, hpay', hpre, hI, hIdef, hchecked,
        harm', hIsigma, hIcut, hIscan', hfreeze, hbase, hcut, hnonempty, hpartition, ?_⟩
      change seg.records ++ seg.remaining = R.drop e at hpartition
      choose done cells hcell using (fun j : Fin seg.records.length =>
        hcover seg.records[j.val] (List.getElem_mem j.isLt))
      let D : List (RoundInput p.K) := List.ofFn cells
      have hD : D.length = seg.records.length := List.length_ofFn
      have hcD (j : Fin seg.records.length) :
          laterCollectionReadout s seg.records[j.val] = some (D[j.val]'(by omega)) := by
        simpa only [D, List.getElem_ofFn] using (hcell j).2.2.1
      have hcell0D (j : Fin seg.records.length) := cell0_of_collection s _ _ (hcD j)
      have hinput (j : Fin seg.records.length) : ∃ d : CompletedRound rate,
          extractRound seg.records[j.val] = some d ∧
          ∀ a, CoordinatorCollectionLedger.localQueueRecord l0
            d.input.round d.input.enabled d.input.raw a =
              ((D[j.val]'(by omega)).enabled,
                quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) (D[j.val]'(by omega)) a) := by
        obtain ⟨hext, _hu, _hr, _hp, hs, hcutoff, hf, hen, hdate, _hrate, _hrw,
          _hrows, _hJ, _hrewards, out, _hcall, _hrun, _hrecorder, _hgate, _hraw,
          harrival, _hphysical, hdisabled, _hphysicalRaw⟩ := hcell j
        refine ⟨done j, hext, ?_⟩
        intro a
        simpa only [D, List.getElem_ofFn] using completed_queue_record l0 _ (done j) (cells j)
          hext hs hcutoff hf hen hdate harrival (fun h => (hdisabled h).2) a
      have hphysical (a : Fin p.K) : seg.records.map (physicalQueueRecord l0 a) =
          D.map (fun cell => (cell.enabled,
            quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) := by
        apply List.ext_getElem
        · simp only [List.length_map, hD]
        · intro j hj hj'
          have hjr : j < seg.records.length := by simpa only [List.length_map] using hj
          obtain ⟨_hext, _hu, _hr, _hp, _hs, _hcutoff, _hf, _hen, _hdate, _hrate, _hrw,
            _hrows, _hJ, _hrewards, out, _hcall, _hrun, _hrecorder, _hgate, _hraw,
            _harrival, _hphysical, _hdisabled, hphysicalRaw⟩ := hcell ⟨j, hjr⟩
          simpa only [List.getElem_map, D, List.getElem_ofFn] using hphysicalRaw a
      have hne : seg.records ≠ [] := by
        obtain ⟨during, hduring⟩ := hnonempty
        rw [hduring]
        exact List.cons_ne_nil _ _
      obtain ⟨hq, _hwhole, _hpayload, saved, hend, hcursor, during, _hduring,
        htake, _hnotlater, _hduringNot, _hpending, _hnodup, _hwitnesses, hboundary⟩ :=
        ReferenceFirstCorrectedReplacementCollectionBoundaryHistory.firstCell_collection_boundary_history
          rate rewards C_star C_h u t z hz e seg hseg hne hcut
      let q := e + seg.records.length
      let G := A ++ D
      change q ≤ R.length at hq
      have hG : G.length = q := by simp only [G, List.length_append, hAlen, hD]; rfl
      have hrecords (j : Fin seg.records.length) : R[e + j.val]? = some seg.records[j.val] := by
        have hget := congrArg (fun L => L[j.val]?) hpartition
        rw [List.getElem?_append_left j.isLt, List.getElem?_eq_getElem j.isLt,
          List.getElem?_drop] at hget
        simpa only [Nat.add_comm] using hget.symm
      have hprefixG := prefixInputs_append_records rewards C_star C_h z e A D seg.records
        hprefixA' hD hrecords hcell0D
      have hcoordinates := calendar_coordinates rewards C_star C_h z q G hG hq hprefixG
      have hT : s + q ≤ p.T := by
        have hlenR := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
        change R.length = p.T - s at hlenR
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
        change s ≤ p.T at hs
        omega
      refine ⟨D, hD, ?_, ?_, hG, hq, hT, htake, hprefixG,
        hcoordinates.1, hcoordinates.2, ?_, ?_, saved, hend, hcursor, hboundary⟩
      · intro j
        refine ⟨hcell0D j, done j, ?_⟩
        simpa only [D, List.getElem_ofFn, hroutR] using hcell j
      · intro a
        refine ⟨inputQueueRecords_eq_cells l0 seg.records D hD hinput a, hphysical a, ?_⟩
        intro h
        rw [List.map_take, hphysical a, ← List.map_take]
      · intro a
        have hA_disabled : ∀ cell ∈ A, cell.enabled = false → ∀ arm,
            quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm = 0 := by
          intro cell hmem hfalse
          exact (hcoordinates.2 cell (List.mem_append_left D hmem) hfalse).2
        refine ⟨unstopped_word_eq_raw A hA_disabled a,
          unstopped_word_eq_raw (A.take (e - 1)) (fun cell hmem =>
            hA_disabled cell (List.mem_of_mem_take hmem)) a, ?_⟩
        intro h
        exact unstopped_word_eq_raw (G.take h) (fun cell hmem hfalse =>
          (hcoordinates.2 cell (List.mem_of_mem_take hmem) hfalse).2) a
      · intro raw U hempty a
        have hnum := firstCell_segment_replay_values rewards C_star C_h u t z hz
          L c birth hL hc hb rout qout beta hlive htT hk hstate hlater he seg I hseg hI hempty a
        have hDn : D ≠ [] := by
          intro hd
          have hzero : seg.records.length = 0 := by rw [← hD, hd]; rfl
          exact hne (List.length_eq_zero_iff.mp hzero)
        have hGE : G.take e = A := by simpa only [G, ← hAlen] using (List.take_append_length (l₁ := A) (l₂ := D))
        have hGEprev : G.take (e - 1) = A.take (e - 1) :=
          List.take_append_of_le_length (by omega)
        have hGq : G.take q = G := List.take_of_length_le (by omega)
        have hGprev : G.take (q - 1) = A ++ D.take (D.length - 1) := by
          simpa only [G, hG] using take_before_last_append A D hDn
        have hAdis : ∀ cell ∈ A, cell.enabled = false → ∀ arm,
            quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm = 0 := by
          intro cell hmem hfalse
          exact (hcoordinates.2 cell (List.mem_append_left D hmem) hfalse).2
        have hrawA := unstopped_word_eq_raw A hAdis a
        have hrawPrev := unstopped_word_eq_raw (A.take (e - 1)) (fun cell hmem =>
          hAdis cell (List.mem_of_mem_take hmem)) a
        have hH := inputQueueRecords_eq_cells l0 seg.records D hD hinput a
        change CollectionKnownQueueContinuation.inputQueueRecords l0 a seg.inputs = raw a D at hH
        have hHphys := hphysical a
        have hHprev : (seg.records.take (seg.records.length - 1)).map (physicalQueueRecord l0 a) =
            raw a (D.take (D.length - 1)) := by
          rw [List.map_take, hHphys, ← hD, ← List.map_take]
        have hUe : U a e = QueueReplay.replay (4 * rate.n) (0, 0) (raw a A) := by
          change QueueReplay.replay (4 * rate.n) (0, 0) (raw a (G.take e)) = _
          rw [hGE]
        have hUprev : U a (e - 1) = QueueReplay.replay (4 * rate.n) (0, 0) (raw a (A.take (e - 1))) := by
          change QueueReplay.replay (4 * rate.n) (0, 0) (raw a (G.take (e - 1))) = _
          rw [hGEprev]
        have hUq : U a q = QueueReplay.replay (4 * rate.n) (0, 0) (raw a G) := by
          change QueueReplay.replay (4 * rate.n) (0, 0) (raw a (G.take q)) = _
          rw [hGq]
        have hUqprev : U a (q - 1) = QueueReplay.replay (4 * rate.n) (0, 0)
            (raw a (A ++ D.take (D.length - 1))) := by
          change QueueReplay.replay (4 * rate.n) (0, 0) (raw a (G.take (q - 1))) = _
          rw [hGprev]
        rcases hnum with ⟨_j, _hja, hcutoff, hcurrent, hincrement, _hlenI, _hlenR, _hpos, hlast⟩ |
          ⟨i, _hia, k, _up, _hek, _hkv, _hmem, _hacc, _hupsigma, cA, _hcA, hpayA, harmA,
            _IA, _hIA, _hIAeq, _hchecked, hN, _hwtime, hw, v, ho, hv, _hfollowers,
            hc0, hs0, hshort0, f, _head0, _valid0, D0, _hhead0, _hpay0, hD0,
            hsource, hell, hcutoff, hcurrent, hincrement⟩
        · let E := A.map (fun cell => UnstoppedRecordedQueueComparison.unstoppedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)
          let Eprev := (A.take (A.length - 1)).map (fun cell =>
            UnstoppedRecordedQueueComparison.unstoppedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)
          let H := CollectionKnownQueueContinuation.inputQueueRecords l0 a seg.inputs
          let V := QueueReplay.replay (4 * rate.n) (0, 0) E
          let Vprev := QueueReplay.replay (4 * rate.n) (0, 0) Eprev
          let Q := QueueReplay.replay (4 * rate.n) (0, 0) (E ++ H)
          let last := CollectionKnownQueueContinuation.replayLastService
            (4 * rate.n) (0, V.2) (V.1 - Vprev.1) H
          simp only [hpre] at hcutoff hcurrent hincrement hlast
          change seg.final.cutoffRegisters a = some ⟨V.1, V.2, V.1 - Vprev.1⟩ at hcutoff
          change seg.final.currentRegisters a = some ⟨Q.2, last⟩ at hcurrent
          change V.1 + seg.final.increment a = Q.1 at hincrement
          change last = (QueueReplay.replay (4 * rate.n) (0, V.2) H).1 -
            (QueueReplay.replay (4 * rate.n) (0, V.2) (H.take (H.length - 1))).1 at hlast
          dsimp only [V, Vprev, Q, last, E, Eprev, H] at hcutoff hcurrent hincrement hlast
          simp only [hAlen, hrawA, hrawPrev, hH] at hcutoff hcurrent hincrement hlast
          have hlast' := hlast.trans (replay_tail_difference (4 * rate.n) (raw a A) (raw a D))
          have hwordPrev : raw a A ++ (raw a D).take ((raw a D).length - 1) =
              raw a (A ++ D.take (D.length - 1)) := by
            simp only [raw, List.length_map, ← List.map_take, List.map_append]
          rw [hwordPrev] at hlast'
          rw [hlast'] at hcurrent
          have hresult : seg.final.cutoffRegisters a = some ⟨(U a e).1, (U a e).2,
              (U a e).1 - (U a (e - 1)).1⟩ ∧
              seg.final.currentRegisters a = some ⟨(U a q).2, (U a q).1 - (U a (q - 1)).1⟩ ∧
              (U a e).1 + seg.final.increment a = (U a q).1 := by
            rw [hUe, hUprev, hUq, hUqprev]
            exact ⟨by simpa only [raw] using hcutoff,
              by simpa only [G, raw, List.map_append] using hcurrent,
              by simpa only [G, raw, List.map_append] using hincrement⟩
          refine ⟨hresult.1, hresult.2.1, hresult.2.2, ?_⟩
          exact Or.inl ⟨_j, _hja, hrawA, hrawPrev, hH⟩
        · let P := cA.payload
          let N := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) - (P.sigma.val + 1)
          let window := (R.drop b).take N
          let Cells : Fin N → RoundInput p.K := fun n => ReferenceFirstWindowNumericalStream.sourceCell
            (window[n.val]'(Nat.lt_of_lt_of_eq n.isLt hw.symm)) (v n).view.payload (v n).view.pendingAtChoice
            (ReferenceLaterLiveNumericalReadout.preparedStates _ (ho n))
            (v n).view.complementWeights (v n).view.cutoff
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v n))
          let Ai := List.ofFn (fun n => ((Cells n).enabled,
            quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) (Cells n) a))
          let Cells0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z rewards C_star C_h hc0
            (p.T - s) hs0
          let E0 := ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0)
          have hP : P = rout.payload := hpayA.trans hpay'
          have hCells : List.ofFn Cells = [c] ++ B :=
            assigned_live_cells_eq rewards C_star C_h z b e L B c hLb hAlen heR hprefixA'
              P (by rw [hP]; exact hlater) N hN hw v ho hv
          have hstart : Cells0 ++ D0 = L := stream_cells_eq_past rewards C_star C_h u t z hz L hL
            hc0 hs0 hshort0 f D0 hD0 (fun n => by
              obtain ⟨call, valid, hcall, _hpay, hcell, _⟩ := hsource n
              exact ⟨call, valid, hcall, hcell⟩) hell
          have hAi : Ai = raw a ([c] ++ B) := by
            simpa only [Ai, raw, List.map_ofFn, Function.comp_def] using congrArg (List.map
              (fun cell => (cell.enabled,
                quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a))) hCells
          have hE0 : E0 = raw a L := by
            change ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (Cells0 ++ D0) = raw a L
            rw [hstart]
            rfl
          have hE : E0 ++ Ai = raw a A := by rw [hE0, hAi]; simp only [A, raw, List.map_append, List.append_assoc]
          have hAiLen : Ai.length = N := List.length_ofFn
          have hAiPos : 0 < Ai.length := by
            have hClen := congrArg List.length hCells
            simp only [List.length_ofFn, List.length_append, List.length_singleton] at hClen
            omega
          have hElen : (E0 ++ Ai).length = e := by rw [hE, List.length_map]; exact hAlen
          have hEprev : E0 ++ Ai.take (N - 1) = raw a (A.take (e - 1)) := by
            calc
              _ = (E0 ++ Ai).take (e - 1) := by
                simpa only [hElen, hAiLen] using
                  (take_before_last_append E0 Ai (List.length_pos_iff.mp hAiPos)).symm
              _ = (raw a A).take (e - 1) := congrArg (List.take (e - 1)) hE
              _ = _ := by simp only [raw, List.map_take]
          dsimp only at hcutoff hcurrent hincrement
          simp only [harmA] at hcutoff hcurrent hincrement
          change seg.final.cutoffRegisters a = some ⟨(QueueReplay.replay (4 * rate.n) (0, 0) (E0 ++ Ai)).1,
            (QueueReplay.replay (4 * rate.n) (0, 0) (E0 ++ Ai)).2,
            (QueueReplay.replay (4 * rate.n) (0, 0) (E0 ++ Ai)).1 -
              (QueueReplay.replay (4 * rate.n) (0, 0) (E0 ++ Ai.take (N - 1))).1⟩ at hcutoff
          rw [hE, hEprev] at hcutoff
          have hpreledger : seg.context.preLedger = l0 := hpre
          rw [hpreledger] at hcurrent hincrement
          change seg.final.currentRegisters a = some ⟨(QueueReplay.replay (4 * rate.n) (0, 0)
              ((E0 ++ Ai) ++ seg.records.map (physicalQueueRecord l0 a))).2,
            (QueueReplay.replay (4 * rate.n) (0, 0) ((E0 ++ Ai) ++ seg.records.map (physicalQueueRecord l0 a))).1 -
              (QueueReplay.replay (4 * rate.n) (0, 0) ((E0 ++ Ai) ++
                (seg.records.take (seg.records.length - 1)).map (physicalQueueRecord l0 a))).1⟩ at hcurrent
          change (QueueReplay.replay (4 * rate.n) (0, 0) (E0 ++ Ai)).1 + seg.final.increment a =
            (QueueReplay.replay (4 * rate.n) (0, 0) ((E0 ++ Ai) ++ seg.records.map (physicalQueueRecord l0 a))).1 at hincrement
          rw [hE, hHphys, hHprev] at hcurrent
          rw [hE, hHphys] at hincrement
          have hresult : seg.final.cutoffRegisters a = some ⟨(U a e).1, (U a e).2,
              (U a e).1 - (U a (e - 1)).1⟩ ∧
              seg.final.currentRegisters a = some ⟨(U a q).2, (U a q).1 - (U a (q - 1)).1⟩ ∧
              (U a e).1 + seg.final.increment a = (U a q).1 := by
            rw [hUe, hUprev, hUq, hUqprev]
            exact ⟨by simpa only [raw] using hcutoff,
              by simpa only [G, raw, List.map_append] using hcurrent,
              by simpa only [G, raw, List.map_append] using hincrement⟩
          refine ⟨hresult.1, hresult.2.1, hresult.2.2, ?_⟩
          have hN' : N = 1 + W.length := by change N = e - b at hN; dsimp only [e] at hN; omega
          have hwindowEq : window = birth :: W := by
            dsimp only [window]
            rw [hN']
            exact window_eq_birth_cons rewards C_star C_h z b birth hb hk
          refine Or.inr ⟨i, _hia, k, _up, _hek, _hkv, _hmem, _hacc, _hupsigma,
            cA, _hcA, hpayA, harmA, _IA, _hIA, _hIAeq, _hchecked,
            hP, hN', hwindowEq, hw, Cells, ?_, hCells,
            hc0, hs0, hshort0, f, D0, hD0, ?_, hstart, hE0, hAi, hE, hEprev, hHphys, hHprev⟩
          · intro n
            let r := window[n.val]'(Nat.lt_of_lt_of_eq n.isLt hw.symm)
            obtain ⟨hselected, hpay, _hcut, hlive⟩ := hv n
            change r.output.preparation.coordinator.selection = some (v n) at hselected
            change CoordinatorLocalArmChoice.assignmentIsLive (v n).view.payload (v n).view.cutoff r.input.time at hlive
            have hpayR : (v n).view.payload = rout.payload := hpay.trans hP
            have hbase : s < (v n).view.payload.sigma.val := by rw [hpayR]; exact hlater
            have hor : ReferenceLaterLiveNumericalReadout.preparedOrdinary r := ho n
            have hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some (Cells n) := by
              unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
              simp only [hselected, hbase, hlive, and_self, ite_true, dite_eq_left hor]
              rfl
            exact ⟨hread, cell0_of_live s r (Cells n) hread⟩
          · intro n
            obtain ⟨call, valid, hcall, _hpay, hcell, _⟩ := hsource n
            exact ⟨call, valid, hcall, hcell⟩

end Bandits.Support.ReferenceFirstCorrectedCollectionCalendarNumericalJoin
