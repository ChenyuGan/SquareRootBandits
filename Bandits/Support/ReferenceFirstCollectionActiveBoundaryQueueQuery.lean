/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPendingObservation
public import Bandits.Support.ReferenceCompleteObservationPrefixInformation

/-!
# Actual first-collection active boundaries and strict-past queue queries

Sources: `06_interruptions.tex:355-408,425-431,477-487`,
`05_binary_transport.tex:180-240`, and
`appendix_a_local_protocol.tex:44-64,100-108` in the pinned ZIP4 manuscript.
The support event reads only the actual incoming state. Numerical queries
retain every arm and every earlier calendar prefix, including disabled rounds.
These are internal support results, without a stopped-phase or regret claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionActiveBoundaryQueueQuery

open ReferenceCompleteFirstPhaseObservationRecovery
open ReferenceLaterCollectionSourceReadoutMeasurability

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

/-- Literal analytical support at a fixed first-assignment start and cutoff.
All constructor fields are read from the actual incoming record. -/
def C (s u : ℕ) (t : Fin p.T) : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  {z | ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s ∧
    ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      match r.input.state.coordinator with
      | .live reg _ _ =>
          t.val = u ∧ reg.payload.sigma.val = s ∧
            ReferenceCollectionPhaseHistory.cutoffChosen r.input = true
      | .collection payload ledger _ =>
          u < t.val ∧ payload.sigma.val = s ∧ ledger.cutoff = u + 1 ∧ ledger.pending.Nonempty
      | .first | .dagger => False}

variable {rate rewards C_star C_h}

/-- Support implies actual pending activity; no pending truth is assumed. -/
theorem C_subset_Praw (s u : ℕ) (t : Fin p.T) :
    C rate rewards C_star C_h s u t ⊆
      {z | (ReferenceFirstCollectionPendingObservation.Praw
        rate rewards C_star C_h t.val z).Nonempty} := by
  rintro z ⟨hs, r, hr, hb⟩
  change (ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h t.val z).Nonempty
  rw [ReferenceFirstCollectionPendingObservation.Praw_at, hs]
  unfold ReferenceFirstCollectionPendingObservation.Q
  simp only [hr]
  cases hc : r.input.state.coordinator with
  | first => simp only [hc] at hb
  | dagger => simp only [hc] at hb
  | live reg owned base =>
      simp only [hc] at hb
      simp only [ite_eq_left hb.2]
      exact ⟨⟨0, by have h := p.two_le_m; omega⟩, Finset.mem_univ _⟩
  | collection payload ledger saved =>
      simp only [hc] at hb
      simp only [ite_eq_left hb.2.1]
      exact hb.2.2.2

private def codeBoundary (u : ℕ) (t : Fin p.T)
    (code : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate) : Bool :=
  match code with
  | .inr (.inl _) => decide (t.val = u)
  | .inr (.inr (.inl (_, ledger, _))) => decide (u < t.val ∧ ledger.cutoff = u + 1)
  | _ => false

private def boundaryObservation (u : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Bool :=
  ((ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z).map
    (fun code => codeBoundary u t code.1)).getD false

private theorem measurable_codeBoundary (u : ℕ) (t : Fin p.T) :
    Measurable (codeBoundary (rate := rate) u t) := by
  have hcollection : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) =>
      decide (u < t.val ∧ z.2.1.cutoff = u + 1)) :=
    (measurable_of_countable (fun z : ReferenceActivePhysicalStep.Ledger rate ×
      Option (Fin p.T × Bool) => decide (u < t.val ∧ z.1.cutoff = u + 1))).comp measurable_snd
  exact Measurable.sumElim measurable_const
    (measurable_const.sumElim (hcollection.sumElim measurable_const))

private theorem boundaryObservation_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u : ℕ) (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (boundaryObservation (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) u t) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)
  have hm := ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun v : ReferenceActivePhysicalStepMeasurability.StateCode p rate ×
      BootstrapPrivateRoundStreams.SourceInput p => codeBoundary u t v.1.1)
    ((measurable_codeBoundary u t).comp (measurable_fst.comp measurable_fst))
    _ (ReferenceSourcePrefixHistoryFiltration.incoming_measurable
      rate rewards C_star C_h control0 t)
  have hg : Measurable (fun b : Option Bool => b.getD false) := by
    have h := (Measurable.sumElim measurable_id measurable_const :
      Measurable (Sum.elim id (fun _ : PUnit => false))).comp
        (comap_measurable (Equiv.optionEquivSumPUnit Bool))
    convert h using 1
    funext b
    cases b <;> rfl
  exact hg.comp hm

private theorem C_iff_observations (s u : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    z ∈ C rate rewards C_star C_h s u t ↔
      z ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s ∧
      (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h s t z).Nonempty ∧
      boundaryObservation (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) u t z = true := by
  have hlocal : z ∈ C rate rewards C_star C_h s u t ↔
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s ∧
      (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h s t z).Nonempty ∧
      boundaryObservation (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) u t z = true := by
    simp only [C, Set.mem_ofPred_eq]
    unfold boundaryObservation ReferenceSourcePrefixHistoryFiltration.incoming
      ReferenceFirstCollectionPendingObservation.Q
    cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none => simp
    | some r =>
        simp only [Option.some.injEq]
        cases hc : r.input.state.coordinator with
        | first => simp [ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator, codeBoundary, hc]
        | dagger => simp [ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator, codeBoundary, hc]
        | live reg owned base =>
            have hu : (Finset.univ : Finset (Fin (p.m - 1))).Nonempty :=
              ⟨⟨0, by have h := p.two_le_m; omega⟩, Finset.mem_univ _⟩
            simp only [Option.map_some, Option.getD_some,
              ReferenceActivePhysicalStepMeasurability.encodeState,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, codeBoundary,
              decide_eq_true_eq]
            split_ifs <;> simp_all [and_comm, and_assoc]
        | collection payload ledger saved =>
            simp only [Option.map_some, Option.getD_some,
              ReferenceActivePhysicalStepMeasurability.encodeState,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, codeBoundary,
              decide_eq_true_eq]
            split_ifs <;> simp_all [and_comm, and_assoc]
  rw [hlocal]
  constructor
  · rintro ⟨hs, hQ, hb⟩
    have hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z := by
      by_contra hnot
      rw [ReferenceFirstCollectionPendingObservation.Q_eq_empty_of_not_launchBy _ t z hnot] at hQ
      exact Finset.not_nonempty_empty hQ
    exact ⟨⟨hz.1, hs⟩, hQ, hb⟩
  · rintro ⟨⟨_, hs⟩, hQ, hb⟩
    exact ⟨hs, hQ, hb⟩

/-- Adaptation uses the actual launch stratum and incoming state, including
cutoff resets. It does not inspect the current sampler or recorder draws. -/
theorem C_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (s u : ℕ) (t : Fin p.T) (hs : s ≤ u) (hu : u ≤ t.val) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (C rate rewards C_star C_h s u t) := by
  have heq : C rate rewards C_star C_h s u t =
      ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s ∩
      {z | (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h s t z).Nonempty} ∩
      {z | boundaryObservation (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) u t z = true} := by
    ext z
    rw [C_iff_observations]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
  rw [heq]
  exact ((ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_measurable
    rate rewards C_star C_h control0 t s (hs.trans hu)).inter
      ((ReferenceFirstCollectionPendingObservation.Q_measurable control0 s t)
        (Set.to_countable {v : Finset (Fin (p.m - 1)) | v.Nonempty}).measurableSet)).inter
    ((boundaryObservation_measurable control0 u t) (measurableSet_singleton true))

/-- A dated raw numerical lookup. Absence stays an outer or inner `none`. -/
def numericalLookup (rate : ReferenceActivePhysicalStep.RateInput p)
    (s u k : ℕ) (omega : OBS rate) :
    Option (ℕ × Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)) :=
  ((if s + k < u then rawLiveNumericalDecoder rate omega
    else rawCollectionNumericalDecoder rate omega)[k]?).map (fun e => (e.1.val, e.2))

/-- Full-coordinate agreement at every original date, through the current
cell. The list before the final cell has exactly the strict-past length. -/
def Matches (rate : ReferenceActivePhysicalStep.RateInput p)
    (s u : ℕ) (t : Fin p.T) (omega : OBS rate)
    (N : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K) : Prop :=
  N.length = t.val - s ∧
    ∀ k (hk : k < (N ++ [c]).length),
      numericalLookup rate s u k omega =
        some (s + k, some (numericalCoordinates ((N ++ [c])[k])))

private theorem numericalCoordinates_injective :
    Function.Injective (numericalCoordinates (p := p)) := by
  intro a b h
  have he := congrArg Prod.fst h
  have ha := congrArg (fun x => x.2.1) h
  have hr := congrArg (fun x => x.2.2.1) h
  have hx := congrArg (fun x => x.2.2.2) h
  cases a
  cases b
  cases he
  cases ha
  cases hr
  cases hx
  rfl

/-- A present raw coordinate fixes the whole chronological pair, including
both real vectors, rather than separate witnesses for separate arms. -/
theorem matches_unique (s u : ℕ) (t : Fin p.T) (omega : OBS rate)
    {N M : List (RecordedQueueRun.RoundInput p.K)}
    {c d : RecordedQueueRun.RoundInput p.K}
    (hN : Matches rate s u t omega N c) (hM : Matches rate s u t omega M d) :
    (N, c) = (M, d) := by
  have hlen : N.length = M.length := hN.1.trans hM.1.symm
  have hfull : N ++ [c] = M ++ [d] := by
    apply List.ext_getElem (by simp only [List.length_append, List.length_singleton, hlen])
    intro k hk hk'
    have he := Option.some.inj ((hN.2 k hk).symm.trans (hM.2 k hk'))
    exact numericalCoordinates_injective (Option.some.inj (congrArg Prod.snd he))
  obtain ⟨hNM, hcd⟩ := List.append_inj hfull hlen
  exact Prod.ext hNM (List.singleton_inj.mp hcd)

private theorem matches_of_raw_prefixes (s u : ℕ) (t : Fin p.T)
    (omega : OBS rate) (live D : List (RecordedQueueRun.RoundInput p.K))
    (k : ℕ) (hk : k < D.length)
    (hu : u = s + live.length) (ht : t.val = s + live.length + k)
    (hLive : ∀ j (hj : j < live.length),
      ((rawLiveNumericalDecoder rate omega)[j]?).map (fun e => (e.1.val, e.2)) =
        some (s + j, some (numericalCoordinates live[j])))
    (hCollection : ∀ j (hj : j < D.length),
      ((rawCollectionNumericalDecoder rate omega)[live.length + j]?).map
        (fun e => (e.1.val, e.2)) =
        some (s + live.length + j, some (numericalCoordinates D[j]))) :
    Matches rate s u t omega (live ++ D.take k) D[k] := by
  have hfull : (live ++ D.take k) ++ [D[k]] = live ++ D.take (k + 1) := by
    rw [List.append_assoc, List.take_succ_eq_append_getElem hk]
  constructor
  · simp only [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    omega
  · intro j hj
    have hjlen : j < live.length + (k + 1) := by
      simpa only [hfull, List.length_append, List.length_take,
        Nat.min_eq_left (show k + 1 ≤ D.length by omega)] using hj
    by_cases hjlive : j < live.length
    · have hcell : ((live ++ D.take k) ++ [D[k]])[j] = live[j] := by
        simp only [hfull, List.getElem_append_left hjlive]
      rw [hcell]
      unfold numericalLookup
      rw [ite_eq_left (show s + j < u by omega)]
      exact hLive j hjlive
    · have hjD : j - live.length < D.length := by omega
      have hcell : ((live ++ D.take k) ++ [D[k]])[j] = D[j - live.length] := by
        simp only [hfull, List.getElem_append_right (as := live) (Nat.le_of_not_gt hjlive),
          List.getElem_take]
      rw [hcell]
      unfold numericalLookup
      rw [ite_eq_right (show ¬ s + j < u by omega)]
      have hindex : live.length + (j - live.length) = j := by omega
      simpa only [hindex, Nat.add_assoc] using hCollection (j - live.length) hjD

section ActualWindow

variable (z : BootstrapPrivateRoundStreams.SourceInput p)
variable (hcross : (ReferenceInitializationRun.output
  (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)

local notation "start" => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "count" =>
  (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
local notation "span" => firstPhaseReadySpan rate rewards C_star C_h z
local notation "w" =>
  (List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceActivePhysicalHorizon.Run.records
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z rewards C_star C_h hcross
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (firstPhaseReadySpan rate rewards C_star C_h z)))))
local notation "B" =>
  (ReferenceCollectionPhaseHistory.collectionWindow
    (ReferenceActivePhysicalHorizon.Run.records
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z rewards C_star C_h hcross
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (firstPhaseReadySpan rate rewards C_star C_h z)))
    (List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.Run.records
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          z rewards C_star C_h hcross
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          (firstPhaseReadySpan rate rewards C_star C_h z))))))

variable (hshort :
  (List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceActivePhysicalHorizon.Run.records
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z rewards C_star C_h hcross
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (firstPhaseReadySpan rate rewards C_star C_h z))))) <
    (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
variable (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
  (rate := rate) z rewards C_star C_h
  (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hcross
  (firstPhaseReadySpan rate rewards C_star C_h z) hshort)

private theorem active_window_boundary (s u : ℕ) (t : Fin p.T)
    (hs : s ≤ u) (hu : u ≤ t.val) (hz : z ∈ C rate rewards C_star C_h s u t)
    (k : Fin (B).length) (ht : B[k.val].input.time = t) :
    k.val < d.stream.ell ∧ u = start + w ∧ t.val = start + w + k.val := by
  let out := d.stream
  have hwindow : out.window = B := out.windowIsActual
  have htime : t.val = start + w + k.val := by
    have hh := (out.alignment ⟨k.val, by rw [hwindow]; exact k.isLt⟩).2
    simp only [hwindow, ht] at hh
    change t.val + 1 = start + w + 1 + k.val at hh
    omega
  have hstart : start = s := hz.1
  have hP := C_subset_Praw s u t hz
  change (ReferenceFirstCollectionPendingObservation.Praw rate rewards C_star C_h t.val z).Nonempty at hP
  have hQ : (ReferenceFirstCollectionPendingObservation.Q
      rate rewards C_star C_h start B[k.val].input.time z).Nonempty := by
    simpa only [ReferenceFirstCollectionPendingObservation.Praw_at, ht] using hP
  have hqw := ReferenceFirstCollectionPendingObservation.Q_window
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    z count hcross span hshort d k
  change ReferenceFirstCollectionPendingObservation.Q
    rate rewards C_star C_h start B[k.val].input.time z = _ at hqw
  rw [hqw] at hQ
  have hkell : k.val < out.ell := by
    by_cases hk0 : k.val = 0
    · have hpos := out.positiveLength
      omega
    · rw [ite_eq_right hk0] at hQ
      by_contra hnot
      rw [dite_eq_right (Nat.not_lt.mpr (Nat.le_of_not_gt hnot))] at hQ
      exact Finset.not_nonempty_empty hQ
  have hcurr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some B[k.val] := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
    rw [ite_eq_left (show start ≤ t.val by rw [hstart]; exact hs.trans hu),
      completeSuffixRecords_eq_actualFirstEpoch rate rewards C_star C_h z hcross]
    have hi : t.val - start = w + k.val := by omega
    rw [hi]
    simpa only [hwindow] using
      (out.alignment ⟨k.val, by rw [hwindow]; exact k.isLt⟩).1
  obtain ⟨_, r, hr, hb⟩ := hz
  have heq : r = B[k.val] := Option.some.inj (hr.symm.trans hcurr)
  rw [heq] at hb
  refine ⟨hkell, ?_, htime⟩
  by_cases hk0 : k.val = 0
  · have hhead : B[k.val] = out.cutoff.cut := by
      simpa only [hwindow, hk0] using out.cutoffIsHead
    obtain ⟨execution⟩ := out.cutoffExecution
    rw [hhead, execution.actualLive] at hb
    have hu' : t.val = u := hb.1
    omega
  · obtain ⟨j, r', incoming, cell, _, hr', _, hprevious⟩ :=
      out.cell_at ⟨k.val, hkell⟩ (Nat.pos_of_ne_zero hk0)
    have hrEq : r' = B[k.val] := by
      simp only [hwindow] at hr'
      exact (List.getElem?_eq_some_iff.mp hr').2.symm
    have hcoord := cell.readyInput.1
    rw [hrEq] at hcoord
    rw [hcoord] at hb
    have hcut : incoming.cutoff = start + w + 1 := by
      rw [hprevious, (out.context ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hkell⟩).2.1]
      exact out.cutoff.ledgerCutoff
    have hu' : incoming.cutoff = u + 1 := hb.2.2.1
    omega

end ActualWindow

/-- The literal active incoming event produces every original full-vector
cell, with a unique current/past split. No stream or good-domain premise is
supplied by the caller. -/
theorem existsUnique_matching (s u : ℕ) (t : Fin p.T)
    (hs : s ≤ u) (hu : u ≤ t.val)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ C rate rewards C_star C_h s u t) :
    ∃! pair : List (RecordedQueueRun.RoundInput p.K) × RecordedQueueRun.RoundInput p.K,
      Matches rate s u t
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z) pair.1 pair.2 := by
  have hP := C_subset_Praw s u t hz
  have hcross := ((C_iff_observations s u t z).mp hz).1.1
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let count := p.T - start
  let span := firstPhaseReadySpan rate rewards C_star C_h z
  let E := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) z rewards C_star C_h hcross count span
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h = E.records :=
    completeSuffixRecords_eq_actualFirstEpoch rate rewards C_star C_h z hcross
  let observed := fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)) =>
    ∃ k : Fin (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length).length,
      (ReferenceCollectionPhaseHistory.collectionWindow records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length)[k.val].input.time = t
  have hloc : ∃ k : Fin B.length, B[k.val].input.time = t :=
    Eq.mp (congrArg observed hrecords)
      (ReferenceFirstCollectionPendingObservation.Praw_localization t z hP)
  obtain ⟨k, ht⟩ := hloc
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hshort : w < count := by
    by_contra hnot
    have hB : B = [] := by
      simp only [B, ReferenceCollectionPhaseHistory.collectionWindow,
        List.drop_eq_nil_iff.mpr (show E.records.length ≤ w by omega),
        List.drop_eq_nil_iff.mpr (show E.records.length ≤ w + 1 by omega),
        List.take_nil, List.takeWhile_nil, List.append_nil]
    have hk := k.isLt
    have hlen : B.length = 0 := congrArg List.length hB
    omega
  obtain ⟨_, _, d, _, _, _, D, _, _, _, _, hDlen, _, hcells⟩ :=
    actualFirstCollectionRawObservationIdentity rate rewards C_star C_h z hcross hshort
  obtain ⟨hkell, hcutoff, htime⟩ :=
    active_window_boundary z hcross hshort d s u t hs hu hz k ht
  have hstart : start = s := hz.1
  let live := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hcross count (firstPhaseSpan rate rewards C_star C_h z)
  have hliveWindow : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z rewards C_star C_h hcross count (firstPhaseSpan rate rewards C_star C_h z) =
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records := by
    unfold ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rw [← completeSuffixRecords_eq_actualFirstLiveRun rate rewards C_star C_h z hcross, hrecords]
  have hlivelen : live.length = w := by
    exact (ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate z rewards C_star C_h hcross count (firstPhaseSpan rate rewards C_star C_h z)).trans
        (congrArg List.length hliveWindow)
  have hLive : ∀ j (hj : j < live.length),
      ((rawLiveNumericalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z))[j]?).map (fun e => (e.1.val, e.2)) =
        some (s + j, some (numericalCoordinates live[j])) := by
    obtain ⟨_, _, hlive⟩ := actualFirstLiveRawObservationIdentity rate rewards C_star C_h z hcross
    intro j hj
    have hj' : j < (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate z rewards C_star C_h hcross count (firstPhaseSpan rate rewards C_star C_h z)).length := by
      rw [hliveWindow]
      exact hj.trans_le (Nat.le_of_eq hlivelen)
    obtain ⟨_, hdate, hread, _⟩ := hlive ⟨j, hj'⟩
    have hh := congrArg (Option.map (fun e => (e.1.val, e.2))) hread
    simp only [Option.map_some, hdate] at hh
    change ((rawLiveNumericalDecoder rate
      (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h z))[j]?).map (fun e => (e.1.val, e.2)) =
      some (start + j, some (numericalCoordinates live[j])) at hh
    rw [hstart] at hh
    exact hh
  have hCollection : ∀ j (hj : j < D.length),
      ((rawCollectionNumericalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z))[live.length + j]?).map (fun e => (e.1.val, e.2)) =
        some (s + live.length + j, some (numericalCoordinates D[j])) := by
    intro j hj
    let n : Fin d.stream.ell := ⟨j, by rw [← hDlen]; exact hj⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, hdate,
      _, _, _, _, _, _, _, hread, _⟩ := hcells n
    have hh := congrArg (Option.map (fun e => (e.1.val, e.2))) hread
    simp only [Option.map_some, hdate] at hh
    change ((rawCollectionNumericalDecoder rate
      (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h z))[w + j]?).map (fun e => (e.1.val, e.2)) =
      some (start + w + j, some (numericalCoordinates D[j])) at hh
    rw [hstart] at hh
    simpa only [hlivelen] using hh
  let N := live ++ D.take k.val
  let c := D[k.val]'(by rw [hDlen]; exact hkell)
  have hmatch : Matches rate s u t
      (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h z) N c :=
    matches_of_raw_prefixes s u t _ live D k.val
      (by rw [hDlen]; exact hkell)
      (by rw [hlivelen]; exact hcutoff.trans (congrArg (fun n => n + w) hstart))
      (by rw [hlivelen]; exact htime.trans (congrArg (fun n => n + w + k.val) hstart))
      hLive hCollection
  exact ⟨(N, c), hmatch, fun pair hpair => matches_unique s u t _ hpair hmatch⟩

/-- The matching pair gives a present full-vector cell at each strict-past
original calendar date. -/
theorem matches_past_date (s u : ℕ) (t : Fin p.T) (omega : OBS rate)
    (N : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
    (hmatch : Matches rate s u t omega N c)
    (v : Fin p.T) (hsv : s ≤ v.val) (hvt : v.val < t.val) :
    ((if v.val < u then rawLiveNumericalDecoder rate omega
      else rawCollectionNumericalDecoder rate omega)[v.val - s]?).map
      (fun e => (e.1.val, e.2)) =
        some (v.val, some (numericalCoordinates
          (N[v.val - s]'(by rw [hmatch.1]; omega)))) := by
  have hj : v.val - s < N.length := by rw [hmatch.1]; omega
  have hh := hmatch.2 (v.val - s) (by simp only [List.length_append, List.length_singleton]; omega)
  unfold numericalLookup at hh
  simpa only [Nat.add_sub_of_le hsv, List.getElem_append_left hj] using hh

/-- The current collection cell is present, but is not asserted to be
measurable before the current draws. -/
theorem matches_current_date (s u : ℕ) (t : Fin p.T) (hs : s ≤ u) (hu : u ≤ t.val)
    (omega : OBS rate) (N : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K) (hmatch : Matches rate s u t omega N c) :
    ((rawCollectionNumericalDecoder rate omega)[t.val - s]?).map
      (fun e => (e.1.val, e.2)) = some (t.val, some (numericalCoordinates c)) := by
  have hh := hmatch.2 N.length (by simp only [List.length_append, List.length_singleton]; omega)
  have hd : s + N.length = t.val := by rw [hmatch.1]; omega
  unfold numericalLookup at hh
  simp only [hd, ite_eq_right (show ¬ t.val < u by omega),
    List.getElem_append_right (as := N) (Nat.le_refl _), Nat.sub_self,
    List.getElem_cons_zero] at hh
  simpa only [hmatch.1] using hh

/-- All original unstopped backlog prefixes, on the whole arrival vectors. -/
def allPrefixes (rate : ReferenceActivePhysicalStep.RateInput p)
    (A : List (Bool × (Fin p.K → ℕ))) : Prop :=
  ∀ h : ℕ, h ≤ A.length → ∀ a : Fin p.K,
    32 * (QueueReplay.replay (4 * rate.n) (0, 0)
      ((A.take h).map fun v => (v.1, v.2 a))).2 ≤ D p

/-- The accepted full numerical encoding followed by the all-arm arithmetic. -/
def numericalArrivals (rate : ReferenceActivePhysicalStep.RateInput p)
    (N : List (RecordedQueueRun.RoundInput p.K)) : List (Bool × (Fin p.K → ℕ)) :=
  N.map (arrivalsFromNumerical rate ∘ numericalCoordinates)

private theorem normalized_replay (rate : ReferenceActivePhysicalStep.RateInput p)
    (N : List (RecordedQueueRun.RoundInput p.K)) (h : ℕ) (a : Fin p.K) :
    UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) N h a =
      QueueReplay.replay (4 * rate.n) (0, 0)
        (((numericalArrivals rate N).take h).map fun v => (v.1, v.2 a)) := by
  have hgen (cells : List (RecordedQueueRun.RoundInput p.K)) (initial : ℕ × ℕ) :
      QueueReplay.replay (4 * rate.n) initial
        (cells.map fun c => UnstoppedRecordedQueueComparison.unstoppedRecord
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) =
      QueueReplay.replay (4 * rate.n) initial
        ((numericalArrivals rate cells).map fun v => (v.1, v.2 a)) := by
    induction cells generalizing initial with
    | nil => rfl
    | cons c cells ih =>
        simp only [numericalArrivals, List.map_cons, QueueReplay.replay,
          List.foldl_cons] at ih ⊢
        have hstep : QueueReplay.transition (4 * rate.n) initial
            (UnstoppedRecordedQueueComparison.unstoppedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) =
          QueueReplay.transition (4 * rate.n) initial
            (c.enabled, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) := by
          cases he : c.enabled <;>
            simp [UnstoppedRecordedQueueComparison.unstoppedRecord, he, QueueReplay.transition]
        rw [hstep]
        exact ih _
  simpa only [UnstoppedRecordedQueueComparison.unstoppedReplay,
    numericalArrivals, List.map_take, ReferenceFirstLaunchNumericalCell.queueParameters]
      using hgen (N.take h) (0, 0)

/-- The strict-past all-prefix test is exactly the stopped run's false flag. -/
theorem allPrefixes_iff_noOverflow (rate : ReferenceActivePhysicalStep.RateInput p)
    (N : List (RecordedQueueRun.RoundInput p.K)) :
    allPrefixes rate (numericalArrivals rate N) ↔
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) N).overflow = false := by
  have hflag := UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) N N.length (Nat.le_refl _)
  rw [List.take_length] at hflag
  have heq :
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) N).overflow = false ↔
      N.length < UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) N :=
    Bool.eq_false_iff.trans ((not_congr hflag).trans not_le)
  rw [heq]
  unfold allPrefixes
  simp only [numericalArrivals, List.length_map]
  constructor
  · intro hb
    by_contra hnot
    have hcross := UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) N (Nat.le_of_not_gt hnot)
    obtain ⟨a, ha⟩ := hcross
    rw [normalized_replay] at ha
    exact (Nat.not_lt_of_ge (hb _ (Nat.le_of_not_gt hnot) a)) ha
  · intro hbefore h hh a
    by_cases hz : h = 0
    · subst h
      simp only [List.take_zero, List.map_nil, QueueReplay.replay, List.foldl_nil, Nat.mul_zero, Nat.zero_le]
    · have hn := UnstoppedRecordedQueueComparison.not_replay_crosses_overflow_before_first
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) N h (by omega) hh (by omega)
      by_contra hnot
      exact hn ⟨a, by rw [normalized_replay]; exact Nat.lt_of_not_ge hnot⟩

/-- The appended current input may itself be the first overflow update. -/
theorem noOverflow_iff_before_appended_firstOverflow
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (N : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K) :
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) N).overflow = false ↔
      N.length < UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) (N ++ [c]) := by
  have h := UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) (N ++ [c]) N.length (by simp)
  rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length] at h
  exact Bool.eq_false_iff.trans ((not_congr h).trans not_le)

/-- Select the existing phase coordinate at each retained date. Missing
records and missing numerical readouts remain `none`; no queue cell is filled. -/
def arrivalObservation (rate : ReferenceActivePhysicalStep.RateInput p)
    (s u : ℕ) (omega : OBS rate) : List (Option (Bool × (Fin p.K → ℕ))) :=
  (List.range omega.length).map fun k =>
    ((if s + k < u then rawLiveArrivalDecoder rate omega
      else rawCollectionArrivalDecoder rate omega)[k]?).bind Prod.snd

/-- A literal all-prefix test on present observations. Its witness is an
entire chronological list of all-arm arrivals, with no absent-cell default. -/
def strictPastTest (rate : ReferenceActivePhysicalStep.RateInput p)
    (s u : ℕ) (omega : OBS rate) : Prop :=
  ∃ A : List (Bool × (Fin p.K → ℕ)),
    arrivalObservation rate s u omega = A.map some ∧ allPrefixes rate A

private theorem measurableSingleton_listObservation {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (List α) := by
  have hinj : Function.Injective
      (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := α)) := by
    intro left right h
    apply List.ext_getElem?
    intro n
    have hn := congrFun (congrArg Prod.snd h) n
    change ReferenceActiveHorizonMeasurability.listObservationAt left n =
      ReferenceActiveHorizonMeasurability.listObservationAt right n at hn
    unfold ReferenceActiveHorizonMeasurability.listObservationAt at hn
    cases hl : left[n]? <;> cases hr : right[n]? <;> simp_all
  constructor
  intro records
  have heq : ({records} : Set (List α)) =
      ReferenceActiveHorizonMeasurability.listObservationCoordinates ⁻¹'
        {ReferenceActiveHorizonMeasurability.listObservationCoordinates records} := by
    ext other
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => congrArg _ h, fun h => hinj h⟩
  let : MeasurableSingletonClass (Unit ⊕ α) := ⟨fun tag => by
    cases tag with
    | inl value =>
        simpa only [Set.image_singleton] using (measurableSet_singleton value).inl_image
    | inr value =>
        simpa only [Set.image_singleton] using (measurableSet_singleton value).inr_image⟩
  rw [heq]
  exact (measurableSet_singleton _).preimage
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates

private theorem strictPastTest_measurable (s u : ℕ) :
    MeasurableSet {omega : OBS rate | strictPastTest rate s u omega} := by
  let Arrival := Bool × (Fin p.K → ℕ)
  let : MeasurableSpace (Option Arrival) :=
    ReferenceInitializationMeasurability.optionCountableMeasurableSpace Arrival
  let : MeasurableSingletonClass (Option Arrival) :=
    ReferenceInitializationMeasurability.optionCountableMeasurableSingletonClass Arrival
  let Entry := Fin p.T × Option Arrival
  let : MeasurableSingletonClass (List Entry) := measurableSingleton_listObservation
  have hm : Measurable (fun omega : OBS rate =>
      (omega.length, (rawLiveArrivalDecoder rate omega, rawCollectionArrivalDecoder rate omega))) :=
    (measurable_fst.comp ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates).prodMk
      ((measurable_rawLiveArrivalDecoder rate).prodMk (measurable_rawCollectionArrivalDecoder rate))
  have hset : MeasurableSet {data : ℕ × (List Entry × List Entry) |
      ∃ A : List Arrival,
        (List.range data.1).map (fun k =>
          ((if s + k < u then data.2.1 else data.2.2)[k]?).bind Prod.snd) = A.map some ∧
        allPrefixes rate A} := (Set.to_countable _).measurableSet
  exact hset.preimage hm

private theorem arrivalLookup_of_numericalLookup (s u j : ℕ) (omega : OBS rate)
    (c : RecordedQueueRun.RoundInput p.K)
    (hh : numericalLookup rate s u j omega = some (s + j, some (numericalCoordinates c))) :
    ((if s + j < u then rawLiveArrivalDecoder rate omega
      else rawCollectionArrivalDecoder rate omega)[j]?).bind Prod.snd =
      some (arrivalsFromNumerical rate (numericalCoordinates c)) := by
  have h := congrArg (fun value : Option (ℕ × Option
      (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)) =>
    value.bind (fun e => e.2.map (arrivalsFromNumerical rate))) hh
  unfold numericalLookup at h
  by_cases hj : s + j < u
  · simpa only [hj, ite_true, rawLiveArrivalDecoder, List.getElem?_map,
      Option.bind_map, Function.comp_def, Option.bind_some, Option.map_some] using h
  · simpa only [hj, ite_false, rawCollectionArrivalDecoder, List.getElem?_map,
      Option.bind_map, Function.comp_def, Option.bind_some, Option.map_some] using h

private theorem arrivalObservation_take (s u : ℕ) (t : Fin p.T) (omega : OBS rate)
    (N : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
    (hmatch : Matches rate s u t omega N c)
    (hlen : (omega.take N.length).length = N.length) :
    arrivalObservation rate s u (omega.take N.length) =
      (numericalArrivals rate N).map some := by
  apply List.ext_getElem
  · simp only [arrivalObservation, List.length_map, List.length_range, hlen, numericalArrivals]
  · intro j hj hj'
    have hjN : j < N.length := by
      simpa only [numericalArrivals, List.length_map] using hj'
    have hjfull : j < (N ++ [c]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hnum := hmatch.2 j hjfull
    have harrival := arrivalLookup_of_numericalLookup s u j omega ((N ++ [c])[j]'hjfull) hnum
    simp only [List.getElem_append_left hjN] at harrival
    have hL : (rawLiveArrivalDecoder rate (omega.take N.length))[j]? =
        (rawLiveArrivalDecoder rate omega)[j]? := by
      simp only [rawLiveArrivalDecoder, rawLiveNumericalDecoder, List.getElem?_map,
        List.getElem?_take_of_lt hjN]
    have hR : (rawCollectionArrivalDecoder rate (omega.take N.length))[j]? =
        (rawCollectionArrivalDecoder rate omega)[j]? := by
      simp only [rawCollectionArrivalDecoder, rawCollectionNumericalDecoder, List.getElem?_map,
        List.getElem?_take_of_lt hjN]
    simp only [arrivalObservation, List.getElem_map, List.getElem_range, numericalArrivals]
    by_cases h : s + j < u
    · simpa only [h, ite_true, hL, Function.comp_apply] using harrival
    · simpa only [h, ite_false, hR, Function.comp_apply] using harrival

/-- The strict dated observation has exactly the produced past arrival
vectors, with no use of the current cell or current controls. -/
theorem strictPastTest_iff_allPrefixes (s u : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s)
    (N : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
    (hmatch : Matches rate s u t
      (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h z) N c) :
    strictPastTest rate s u
      (ReferenceCompleteObservationPrefixInformation.datePrefix rate t.val
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z)) ↔ allPrefixes rate (numericalArrivals rate N) := by
  let omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
    rate rewards C_star C_h z
  have hp : ReferenceCompleteObservationPrefixInformation.datePrefix rate t.val omega =
      omega.take N.length := by
    rw [ReferenceCompleteObservationPrefixInformation.datePrefix_eq_take
      rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt), hstart, hmatch.1]
  have hlen : (omega.take N.length).length = N.length := by
    rw [← hp, ReferenceCompleteObservationPrefixInformation.datePrefix_length
      rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt), hstart, hmatch.1]
  have ha := arrivalObservation_take s u t omega N c hmatch hlen
  change strictPastTest rate s u
    (ReferenceCompleteObservationPrefixInformation.datePrefix rate t.val omega) ↔ _
  rw [hp]
  unfold strictPastTest
  rw [ha]
  constructor
  · rintro ⟨A, he, hA⟩
    have heq : numericalArrivals rate N = A :=
      (List.map_injective_iff.mpr (fun _ _ h => Option.some.inj h)) he
    simpa only [heq] using hA
  · intro hA
    exact ⟨numericalArrivals rate N, rfl, hA⟩

/-- Literal strict-past observation test on the original source support. -/
def strictPastEvent (s u : ℕ) (t : Fin p.T) : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  C rate rewards C_star C_h s u t ∩
    {z | strictPastTest rate s u
      (ReferenceCompleteObservationPrefixInformation.datePrefix rate t.val
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z))}

/-- Only the existing strict dated observation supplies the Borel test. -/
theorem strictPastEvent_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (s u : ℕ) (t : Fin p.T) (hs : s ≤ u) (hu : u ≤ t.val) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (strictPastEvent (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) s u t) :=
  (C_measurable control0 s u t hs hu).inter
    ((strictPastTest_measurable s u).preimage
      (ReferenceCompleteObservationPrefixInformation.datePrefix_measurable
        rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt)))

/-- The existential query ranges over matching whole numerical pairs.
Uniqueness is proved by `existsUnique_matching`, rather than stipulated. -/
def queueEvent (s u : ℕ) (t : Fin p.T) : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  {z | z ∈ C rate rewards C_star C_h s u t ∧
    ∃ (N : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K),
      Matches rate s u t
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z) N c ∧ allPrefixes rate (numericalArrivals rate N)}

/-- The existential whole-cell event is the literal strict-past test. -/
theorem queueEvent_eq_strictPastEvent (s u : ℕ) (t : Fin p.T)
    (hs : s ≤ u) (hu : u ≤ t.val) :
    queueEvent (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t =
      strictPastEvent (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t := by
  ext z
  constructor
  · rintro ⟨hC, N, c, hm, hb⟩
    exact ⟨hC, (strictPastTest_iff_allPrefixes s u t z hC.1 N c hm).mpr hb⟩
  · rintro ⟨hC, hb⟩
    obtain ⟨pair, hm, _⟩ := existsUnique_matching s u t hs hu z hC
    exact ⟨hC, pair.1, pair.2, hm,
      (strictPastTest_iff_allPrefixes s u t z hC.1 pair.1 pair.2 hm).mp hb⟩

/-- The requested original-source all-prefix queue event is adapted. -/
theorem queueEvent_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (s u : ℕ) (t : Fin p.T) (hs : s ≤ u) (hu : u ≤ t.val) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (queueEvent (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t) := by
  rw [queueEvent_eq_strictPastEvent s u t hs hu]
  exact strictPastEvent_measurable control0 s u t hs hu

/-- Every matching pair gives the same no-earlier-overflow test. -/
theorem queueEvent_iff_noOverflow (s u : ℕ) (t : Fin p.T)
    (hs : s ≤ u) (hu : u ≤ t.val) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ C rate rewards C_star C_h s u t)
    (N : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
    (hm : Matches rate s u t
      (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h z) N c) :
    z ∈ queueEvent (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t ↔
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) N).overflow = false := by
  rw [queueEvent_eq_strictPastEvent s u t hs hu]
  change (z ∈ C rate rewards C_star C_h s u t ∧ _) ↔ _
  rw [and_iff_right hz, Set.mem_ofPred_eq, strictPastTest_iff_allPrefixes s u t z hz.1 N c hm,
    allPrefixes_iff_noOverflow]

/-- Strictly earlier prefixes are safe exactly before the first crossing in
`N ++ [c]`. A first overflow at the actual current cell remains included. -/
theorem queueEvent_iff_before_current_firstOverflow (s u : ℕ) (t : Fin p.T)
    (hs : s ≤ u) (hu : u ≤ t.val) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ C rate rewards C_star C_h s u t)
    (N : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
    (hm : Matches rate s u t
      (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h z) N c) :
    z ∈ queueEvent (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t ↔
      N.length < UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) (N ++ [c]) :=
  (queueEvent_iff_noOverflow s u t hs hu z hz N c hm).trans
    (noOverflow_iff_before_appended_firstOverflow rate N c)

end Bandits.Support.ReferenceFirstCollectionActiveBoundaryQueueQuery
