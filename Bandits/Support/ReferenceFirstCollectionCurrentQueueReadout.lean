/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentRetainedMoments

import Mathlib.Tactic

/-!
# Original first-call queue readouts

The observations in this module are the optional numerical prefix and the
actual numerical cell at the original first collection call.  Missing launch,
prefix, or current-cell data remain absent.  The scalar backlog functions are
localized analytical observations on the same original source space; they do
not change the physical protocol.

Sources: `04_slow_fast_learner.tex:140-188,245-315`,
`05_binary_transport.tex:352-431`, and `06_interruptions.tex:355-426` under
`sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCurrentQueueReadout

open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)
open ReferenceFirstCollectionCurrentRetainedGate
  (pastCells? prefixReadout? H G acceptedCurrent?)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open ReferenceLaterCollectionSourceReadoutMeasurability
  (numericalCoordinates arrivalCoordinates arrivalsFromNumerical
    arrivalsFromNumerical_numericalCoordinates measurable_arrivalsFromNumerical)

public abbrev QueueReadout (K : ℕ) :=
  (Fin K → ℕ × ℕ) × (Bool × (Fin K → List (Bool × ℕ)))

public abbrev QueueArrivals (K : ℕ) := Bool × (Fin K → ℕ)

public abbrev NumericalCoordinates (p : Parameters) :=
  Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ)))

local instance sourceInputMeasurableSpace {p : Parameters} :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

private instance readoutSumMeasurableSingleton {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton x := by
    cases x with
    | inl a =>
        simpa only [Set.image_singleton] using
          (MeasurableSet.singleton a).inl_image
    | inr b =>
        simpa only [Set.image_singleton] using
          (MeasurableSet.singleton b).inr_image

private instance readoutOptionMeasurableSingleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Option α) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit α))
      (MeasurableSet.singleton (Equiv.optionEquivSumPUnit α x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage,
      (Equiv.optionEquivSumPUnit α).injective.eq_iff]

private instance readoutRecordListMeasurableSingleton :
    MeasurableSingletonClass (List (Bool × ℕ)) where
  measurableSet_singleton l := by
    let : MeasurableSingletonClass (Unit ⊕ (Bool × ℕ)) := ⟨fun x => by
      cases x with
      | inl a =>
          simpa only [Set.image_singleton] using
            (MeasurableSet.singleton a).inl_image
      | inr a =>
          simpa only [Set.image_singleton] using
            (MeasurableSet.singleton a).inr_image⟩
    have hinj : Function.Injective
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates
          (α := Bool × ℕ)) := by
      intro a b h
      have hlen : a.length = b.length := congrArg Prod.fst h
      apply List.ext_getElem hlen
      intro i hi hj
      have he := congrFun (congrArg Prod.snd h) i
      simpa only [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
        ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
        Sum.inr.injEq] using he
    have hm :=
      ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
        (α := Bool × ℕ)
    have hh := hm
      (MeasurableSet.singleton
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates l))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "E" => firstCell rate rewards C_star C_h

local instance (priority := 2000) arrivalsOptionMeasurableSpace :
    MeasurableSpace (Option (QueueArrivals p.K)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

/-- The literal analytical cutoff `1/(32 eta)`. -/
public def Bcap : ℝ := 1 / (32 * rate.eta.val)

/-- The existing optional prefix readout immediately before the current cell. -/
public def before? (t : Fin p.T) (z : SourceInput p) :
    Option (QueueReadout p.K) :=
  ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
    rate rewards C_star C_h t z

/-- The actual optional run readout after appending the existing current cell.
The run always starts at the original launch and is never reset at this call. -/
public def after? (t : Fin p.T) (z : SourceInput p) :
    Option (QueueReadout p.K) :=
  (pastCells? rate rewards C_star C_h t z).bind (fun L =>
    (ReferenceFirstCollectionCurrentNumericalCell.currentCell
      rate rewards C_star C_h t z).map (fun c =>
        stateReadout (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)))

public def normalizedReadoutBacklog
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (observation : Option (QueueReadout p.K)) (a : Fin p.K) : ℝ :=
  match observation with
  | none => 0
  | some r => ((r.1 a).2 : ℝ) /
      ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)

/-- The incoming normalized backlog, localized to the actual first call. -/
public def bMinus (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) : ℝ :=
  (E u t).indicator (fun z =>
    normalizedReadoutBacklog rate
      (before? rate rewards C_star C_h t z) a) z

/-- The post-update normalized backlog, localized to the same actual call. -/
public def bPlus (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) : ℝ :=
  (E u t).indicator (fun z =>
    normalizedReadoutBacklog rate
      (after? rate rewards C_star C_h t z) a) z

/-- The current reflected queue increment, including the service charge. -/
public def x (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) : ℝ :=
  (G rate rewards C_star C_h u t).indicator
    (fun z => ReferenceFirstCollectionCurrentRawMoments.currentRaw
      rate rewards C_star C_h t a z - 4) z

public def acceptedFromReadout (old : QueueReadout p.K)
    (arrival : QueueArrivals p.K) (a : Fin p.K) : Bool × ℕ :=
  if old.2.1 then (false, 0)
  else if arrival.1 then (true, arrival.2 a)
  else (false, 0)

public def readoutUpdate
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (old : QueueReadout p.K)
    (arrival : QueueArrivals p.K) : QueueReadout p.K :=
  let accepted := fun a => acceptedFromReadout old arrival a
  let registers := fun a =>
    QueueReplay.transition
      (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).n)
      (old.1 a) (accepted a)
  (registers,
    old.2.1 || decide (∃ a,
      32 * (registers a).2 >
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).D),
    fun a => old.2.2 a ++ [accepted a])

public def optionalReadoutUpdate
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (old : Option (QueueReadout p.K))
    (arrival : Option (QueueArrivals p.K)) : Option (QueueReadout p.K) :=
  old.bind (fun r => arrival.map (fun v => readoutUpdate rate r v))

public def optionalNumericalUpdate
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (old : Option (QueueReadout p.K))
    (coordinates : Option (NumericalCoordinates p)) : Option (QueueReadout p.K) :=
  optionalReadoutUpdate rate old
    (coordinates.map (arrivalsFromNumerical rate))

private theorem readoutUpdate_actualStep (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) :
    readoutUpdate rate (stateReadout state)
      (arrivalCoordinates rate c) =
        stateReadout (RecordedQueueRun.step
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) state c) := by
  cases state
  rfl

private theorem optionalMap_measurable {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (f : X → Option A) (hf : Measurable f) (g : A → B)
    (hg : Measurable g) : Measurable (fun x => (f x).map g) :=
  ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun v : A × X => g v.1) (hg.comp measurable_fst) f hf

private theorem measurable_readoutUpdate :
    Measurable (fun v : QueueReadout p.K × QueueArrivals p.K =>
      readoutUpdate rate v.1 v.2) := by
  classical
  exact measurable_of_countable _

private theorem measurable_optionalReadoutUpdate :
    Measurable (fun v : Option (QueueReadout p.K) × Option (QueueArrivals p.K) =>
      optionalReadoutUpdate rate v.1 v.2) := by
  classical
  exact measurable_of_countable _

private theorem measurableSet_optionReadout_singleton_gate
    (y : Option (QueueReadout p.K)) :
    @MeasurableSet (Option (QueueReadout p.K))
      ReferenceFirstCollectionCurrentRetainedGate.optionMeasurableSpace {y} := by
  let _ : MeasurableSpace (Option (QueueReadout p.K)) :=
    ReferenceFirstCollectionCurrentRetainedGate.optionMeasurableSpace
  exact MeasurableSet.singleton y

/-- The before readout is measurable in the exact original pre-choice field. -/
theorem before?_measurable (control0 : TimeControl p) (t : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (before? rate rewards C_star C_h t) := by
  let _ : MeasurableSpace (SourceInput p) :=
    sourcePrefixFiltration control0 (t.val + 1)
  let _ : MeasurableSpace (Option (QueueReadout p.K)) :=
    ReferenceInitializationMeasurability.optionCountableMeasurableSpace _
  apply measurable_to_countable'
  intro y
  change MeasurableSet
    ((ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rate rewards C_star C_h t) ⁻¹' {y})
  exact ReferenceFirstCollectionCurrentRetainedGate.prefixReadout_measurable
    rate rewards C_star C_h control0 t
    (measurableSet_optionReadout_singleton_gate y)

/-- The incoming scalar backlog has the same pre-choice measurability. -/
theorem bMinus_measurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (bMinus rate rewards C_star C_h u t a) := by
  let F := sourcePrefixFiltration control0 (t.val + 1)
  have hproject : Measurable (fun v : Option (QueueReadout p.K) =>
      normalizedReadoutBacklog rate v a) := by
    classical
    exact measurable_of_countable _
  have hbase : Measurable[F] (fun z =>
      normalizedReadoutBacklog rate (before? rate rewards C_star C_h t z) a) :=
    hproject.comp (before?_measurable rate rewards C_star C_h control0 t)
  exact hbase.indicator
    (ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t)

/-- The present before observation is also measurable in the ambient original
space. -/
theorem before?_measurable_ambient (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (before? rate rewards C_star C_h t) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  exact Measurable.mono
    (before?_measurable rate rewards C_star C_h control0 t) hle le_rfl

/-- The after observation factors through the countable old state and the
actual optional numerical coordinates, with arrivals computed by the public
source arithmetic. -/
theorem after?_factorization (t : Fin p.T) :
    after? rate rewards C_star C_h t = fun z =>
      optionalNumericalUpdate rate
        (before? rate rewards C_star C_h t z)
        (ReferenceFirstCollectionCurrentNumericalCell.currentCoordinates
          rate rewards C_star C_h t z) := by
  funext z
  unfold after? optionalNumericalUpdate optionalReadoutUpdate before?
  cases hL : pastCells? rate rewards C_star C_h t z with
  | none => simp [hL, ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?]
  | some L =>
      cases hc : ReferenceFirstCollectionCurrentNumericalCell.currentCell
          rate rewards C_star C_h t z with
      | none => simp [hL, hc,
          ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?,
          ReferenceFirstCollectionCurrentNumericalCell.currentCoordinates]
      | some c =>
          have hArr : arrivalsFromNumerical rate
              (ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates c) =
                arrivalCoordinates rate c := by
            change arrivalsFromNumerical rate (numericalCoordinates c) =
              arrivalCoordinates rate c
            exact arrivalsFromNumerical_numericalCoordinates rate c
          simp [hL, hc, ReferenceFirstCollectionCurrentNumericalCell.currentCoordinates,
            ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?,
            hArr, readoutUpdate_actualStep]

/-- The actual post readout is ambient Borel. The optional current cell retains
all continuous coordinates with their existing Borel structures. -/
theorem after?_measurable (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (after? rate rewards C_star C_h t) := by
  rw [after?_factorization]
  have hold : Measurable (before? rate rewards C_star C_h t) :=
    before?_measurable_ambient rate rewards C_star C_h control0 t
  have hcoordinates : Measurable
      (ReferenceFirstCollectionCurrentNumericalCell.currentCoordinates
        rate rewards C_star C_h t) :=
    ReferenceFirstCollectionCurrentNumericalCell.currentCoordinates_measurable
      rate rewards C_star C_h t
  have harrivals : Measurable (fun z =>
      (ReferenceFirstCollectionCurrentNumericalCell.currentCoordinates
        rate rewards C_star C_h t z).map (arrivalsFromNumerical rate)) :=
    optionalMap_measurable _ hcoordinates (arrivalsFromNumerical rate)
      (measurable_arrivalsFromNumerical rate)
  exact (measurable_optionalReadoutUpdate rate).comp
    (hold.prodMk harrivals)

/-- On the original first-call event one actual strict-past list and current
cell determine both optional readouts and the exact accepted current record.
The separate coverage, all-prefix, and accepted-record witnesses are
identified by their same `pastCells? = some L` equations. -/
theorem firstCell_actual_queue_readouts (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K),
      pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t z = some c ∧
      c.enabled = true ∧
      before? rate rewards C_star C_h t z = some (stateReadout (RecordedQueueRun.run q L)) ∧
      after? rate rewards C_star C_h t z =
        some (stateReadout (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) ∧
      acceptedCurrent? rate rewards C_star C_h t a z =
        some (RecordedQueueRun.acceptedRecord q (RecordedQueueRun.run q L) c a) ∧
      (z ∈ H rate rewards C_star C_h t ↔
        ∀ h ≤ L.length, ∀ j : Fin p.K,
          32 * (UnstoppedRecordedQueueComparison.unstoppedReplay
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L h j).2 ≤
              (ReferenceFirstLaunchNumericalCell.queueParameters rate).D) ∧
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t a z =
          ((RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord q (RecordedQueueRun.run q L) c a) : ℝ) /
            ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) ∧
      (∀ k : Fin L.length,
        ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val]? = some r ∧
          r.input.time.val =
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val ∧
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some L[k.val]) := by
  obtain ⟨_, _, _, _, _, _, _, L, _, _, _, _, _, _, _, _, _, _, _, hL,
      _hlen, hcoverage⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
      rate rewards C_star C_h u t z hz
  obtain ⟨Lall, hLall, _hlenAll, hall⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_allPrefixes
      rate rewards C_star C_h u t z hz
  have hAllEq : Lall = L := Option.some.inj (hLall.symm.trans hL)
  subst Lall
  obtain ⟨Lacc, c, hLacc, hc, henabled, haccept, _, _⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_acceptedRecord
      rate rewards C_star C_h u t a z hz
  have haccEq : Lacc = L := Option.some.inj (hLacc.symm.trans hL)
  subst Lacc
  obtain ⟨Lm, cm, hLm, hcm, _hmenabled, _hmall, _hmaccepted, hmraw, _⟩ :=
    ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_eq_acceptedArrival_on_firstCell
      rate rewards C_star C_h u t a z hz
  have hmEq : Lm = L := Option.some.inj (hLm.symm.trans hL)
  subst Lm
  have hcmEq : cm = c := Option.some.inj (hcm.symm.trans hc)
  subst cm
  have hbefore : before? rate rewards C_star C_h t z =
      some (stateReadout (RecordedQueueRun.run q L)) := by
    simp [before?, ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hL]
  have hafter : after? rate rewards C_star C_h t z =
      some (stateReadout (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) := by
    simp [after?, hL, hc]
  have hraw :
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
          rate rewards C_star C_h u t a z =
        ((RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord q (RecordedQueueRun.run q L) c a) : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) := by
    exact hmraw
  refine ⟨L, c, hL, hc, henabled, hbefore, hafter, haccept, hall, hraw, ?_⟩
  exact hcoverage

private theorem firstCell_prefix_rate_floor (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) (hz : z ∈ E u t) :
    ∃ L, pastCells? rate rewards C_star C_h t z = some L ∧
      ∀ round ∈ L, ∀ i : Fin p.K, 32 * rate.eta.val ≤ round.rate i := by
  obtain ⟨L, _, hL, _, _, _, _, _, _, _, hcoverage⟩ :=
    firstCell_actual_queue_readouts rate rewards C_star C_h u t a z hz
  refine ⟨L, hL, ?_⟩
  intro round hround i
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hround
  subst round
  obtain ⟨record, hrecord, _, hcell⟩ := hcoverage ⟨k, hk⟩
  cases hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
  | none =>
      have hcollection :
          ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record =
            some (L[k]) := by
        simpa [ReferenceFirstCollectionCurrentRetainedGate.cell0, hlive] using hcell
      obtain ⟨payload, _, _, _, _, _, _, _, _, _, hrate, _, _, _, _⟩ :=
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call
          0 record (L[k]) hcollection
      have hxi := CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi p
        (eta := rate.eta.val) rate.eta.property payload.anchor i
      have hrate_i : (L[k]).rate i =
          CanonicalRecordingRates.xi p rate.eta.val payload.anchor i := by
        rw [congrFun hrate i, payload.rate_eq_canonical i]
      calc
        32 * rate.eta.val ≤ CanonicalRecordingRates.xi p rate.eta.val
            payload.anchor i := hxi
        _ = (L[k]).rate i := hrate_i.symm
  | some live =>
      have hliveEq : live = L[k] := by
        simpa [ReferenceFirstCollectionCurrentRetainedGate.cell0, hlive] using hcell
      subst live
      obtain ⟨_, selected, _, _, hrate, _⟩ :=
        ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
          0 record (L[k]) hlive
      have hxi := CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi p
        (eta := rate.eta.val) rate.eta.property selected.view.payload.anchor i
      have hrate_i : (L[k]).rate i =
          CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor i := by
        rw [congrFun hrate i, selected.view.payload.rate_eq_canonical i]
      calc
        32 * rate.eta.val ≤ CanonicalRecordingRates.xi p rate.eta.val
            selected.view.payload.anchor i := hxi
        _ = (L[k]).rate i := hrate_i.symm

private theorem currentCell_rate_floor (t : Fin p.T) (z : SourceInput p)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionCurrentNumericalCell.currentCell
      rate rewards C_star C_h t z = some c) :
    ∀ i : Fin p.K, 32 * rate.eta.val ≤ c.rate i := by
  unfold ReferenceFirstCollectionCurrentNumericalCell.currentCell at hc
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none => simp [hr] at hc
  | some record =>
      have hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout
          (ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h) record = some c := by
        simpa [hr] using hc
      obtain ⟨_, selected, _, _, hrate, _⟩ :=
        ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
          (ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h) record c hread
      intro i
      have hxi := CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi p
        (eta := rate.eta.val) rate.eta.property selected.view.payload.anchor i
      have hrate_i : c.rate i =
          CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor i := by
        rw [congrFun hrate i, selected.view.payload.rate_eq_canonical i]
      calc
        32 * rate.eta.val ≤ CanonicalRecordingRates.xi p rate.eta.val
            selected.view.payload.anchor i := hxi
        _ = c.rate i := hrate_i.symm

private theorem before_backlog_bound_on_firstCell (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p) (hz : z ∈ E u t) :
    0 ≤ normalizedReadoutBacklog rate (before? rate rewards C_star C_h t z) a ∧
      normalizedReadoutBacklog rate (before? rate rewards C_star C_h t z) a ≤
        2 * Bcap rate := by
  obtain ⟨L, _, hL, _, _, hbefore, _, _, _, _, _⟩ :=
    firstCell_actual_queue_readouts rate rewards C_star C_h u t a z hz
  rw [hbefore]
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · obtain ⟨Lrate, hLrate, hrate⟩ :=
      firstCell_prefix_rate_floor rate rewards C_star C_h u t a z hz
    have hLsame : Lrate = L := Option.some.inj (hLrate.symm.trans hL)
    subst Lrate
    have hrateQ : ∀ round ∈ L, ∀ i : Fin p.K,
        32 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta ≤ round.rate i := by
      simpa only [ReferenceFirstLaunchNumericalCell.queueParameters] using hrate
    have hbound := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
      q L hrateQ L.length a
    simpa [normalizedReadoutBacklog, stateReadout,
      StoppedQueueBound.normalizedBacklog, Bcap,
      ReferenceFirstLaunchNumericalCell.queueParameters, List.take_length] using hbound

private theorem after_backlog_bound_on_firstCell (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p) (hz : z ∈ E u t) :
    0 ≤ normalizedReadoutBacklog rate (after? rate rewards C_star C_h t z) a ∧
      normalizedReadoutBacklog rate (after? rate rewards C_star C_h t z) a ≤
        2 * Bcap rate := by
  obtain ⟨L, c, hL, hc, _, _, hafter, _, _, _, _⟩ :=
    firstCell_actual_queue_readouts rate rewards C_star C_h u t a z hz
  rw [hafter]
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · obtain ⟨Lrate, hLrate, hrate⟩ :=
      firstCell_prefix_rate_floor rate rewards C_star C_h u t a z hz
    have hLsame : Lrate = L := Option.some.inj (hLrate.symm.trans hL)
    subst Lrate
    have hcrate := currentCell_rate_floor rate rewards C_star C_h t z c hc
    have happendRate : ∀ round ∈ L ++ [c], ∀ i : Fin p.K,
        32 * rate.eta.val ≤ round.rate i := by
      intro round hround i
      rcases List.mem_append.mp hround with hprefix | hcurrent
      · exact hrate round hprefix i
      · have : round = c := by simpa using hcurrent
        subst round
        exact hcrate i
    have happendRateQ : ∀ round ∈ L ++ [c], ∀ i : Fin p.K,
        32 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta ≤ round.rate i := by
      simpa only [ReferenceFirstLaunchNumericalCell.queueParameters] using happendRate
    have hbound := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
      q (L ++ [c]) happendRateQ (L ++ [c]).length a
    have hrun : RecordedQueueRun.run q (L ++ [c]) =
        RecordedQueueRun.step q (RecordedQueueRun.run q L) c := by
      rw [RecordedQueueRun.run, RecordedEpisodeStability.execute_append]
      rfl
    have hboundFull :
        StoppedQueueBound.normalizedBacklog q
          (RecordedQueueRun.run q (L ++ [c])) a ≤
            2 * (1 / (32 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta)) := by
      simpa only [List.take_length] using hbound
    rw [hrun] at hboundFull
    simpa [normalizedReadoutBacklog, stateReadout,
      StoppedQueueBound.normalizedBacklog, Bcap,
      ReferenceFirstLaunchNumericalCell.queueParameters] using hboundFull

/-- Both localized scalar readouts are globally nonnegative and bounded by
the exact twice-cutoff envelope; absence still contributes scalar zero. -/
theorem bMinus_global_bounds (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) :
    0 ≤ bMinus rate rewards C_star C_h u t a z ∧
      bMinus rate rewards C_star C_h u t a z ≤ 2 * Bcap rate := by
  by_cases hz : z ∈ E u t
  · simpa [bMinus, Set.indicator_of_mem hz] using
      before_backlog_bound_on_firstCell rate rewards C_star C_h u t a z hz
  · have heta : 0 < rate.eta.val := rate.eta.property
    rw [bMinus, Set.indicator_of_notMem hz]
    constructor
    · norm_num
    · unfold Bcap
      positivity

theorem bPlus_global_bounds (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) :
    0 ≤ bPlus rate rewards C_star C_h u t a z ∧
      bPlus rate rewards C_star C_h u t a z ≤ 2 * Bcap rate := by
  by_cases hz : z ∈ E u t
  · simpa [bPlus, Set.indicator_of_mem hz] using
      after_backlog_bound_on_firstCell rate rewards C_star C_h u t a z hz
  · have heta : 0 < rate.eta.val := rate.eta.property
    rw [bPlus, Set.indicator_of_notMem hz]
    constructor
    · norm_num
    · unfold Bcap
      positivity

theorem bMinus_bound_on_G (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) (hz : z ∈ G rate rewards C_star C_h u t) :
    bMinus rate rewards C_star C_h u t a z ≤ Bcap rate := by
  rcases hz with ⟨hE, hH⟩
  obtain ⟨L, _, hL, _, _, hbefore, _, _, _, _, _⟩ :=
    firstCell_actual_queue_readouts rate rewards C_star C_h u t a z hE
  have hstate : (RecordedQueueRun.run q L).overflow = false := by
    obtain ⟨readout, hreadout, hflag⟩ := hH
    have hprefix : prefixReadout? rate rewards C_star C_h t z =
        some (stateReadout (RecordedQueueRun.run q L)) := by
      simp [ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hL]
    have heq : readout = stateReadout (RecordedQueueRun.run q L) :=
      Option.some.inj (hreadout.symm.trans hprefix)
    rw [heq] at hflag
    exact hflag
  have hstateTake :
      (RecordedQueueRun.run q (L.take L.length)).overflow = false := by
    simpa only [List.take_length] using hstate
  have hbound := StoppedQueueBound.run_prefix_normalized_backlog_le_threshold_of_overflow_false
    q L L.length a hstateTake
  have hbeforeValue : normalizedReadoutBacklog rate
      (before? rate rewards C_star C_h t z) a =
      StoppedQueueBound.normalizedBacklog q (RecordedQueueRun.run q L) a := by
    rw [hbefore]
    rfl
  rw [bMinus, Set.indicator_of_mem hE, hbeforeValue, Bcap]
  simpa [ReferenceFirstLaunchNumericalCell.queueParameters,
    List.take_length] using hbound

theorem x_eq_retainedRaw_sub_service (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) :
    x rate rewards C_star C_h u t a z =
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
          rate rewards C_star C_h u t a z -
        4 * (G rate rewards C_star C_h u t).indicator (fun _ => (1 : ℝ)) z := by
  by_cases hz : z ∈ G rate rewards C_star C_h u t
  · simp [x, ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw,
      Set.indicator_of_mem hz]
  · simp [x, ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw,
      Set.indicator_of_notMem hz]

private theorem run_overflow_false_of_G (u t : Fin p.T) (_a : Fin p.K)
    (z : SourceInput p) (hz : z ∈ G rate rewards C_star C_h u t)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : pastCells? rate rewards C_star C_h t z = some L) :
    (RecordedQueueRun.run q L).overflow = false := by
  rcases hz with ⟨_, hH⟩
  obtain ⟨readout, hreadout, hflag⟩ := hH
  have hprefix : prefixReadout? rate rewards C_star C_h t z =
      some (stateReadout (RecordedQueueRun.run q L)) := by
    simp [ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hL]
  have heq : readout = stateReadout (RecordedQueueRun.run q L) :=
    Option.some.inj (hreadout.symm.trans hprefix)
  rw [heq] at hflag
  exact hflag

private theorem normalizedReadout_step_reflected (s : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (a : Fin p.K)
    (hstate : s.overflow = false) (henabled : c.enabled = true) :
    normalizedReadoutBacklog rate (some (stateReadout
        (RecordedQueueRun.step q s c))) a =
      max (normalizedReadoutBacklog rate (some (stateReadout s)) a +
        RecordedRoundMoments.rawEstimate q s c a - 4) 0 := by
  have h := CanonicalQueueProcess.normalizedBacklog_step_of_retained
    q s c a hstate henabled
  simpa [normalizedReadoutBacklog, stateReadout,
    StoppedQueueBound.normalizedBacklog] using h

/-- The optional numerical observations implement the reflected queue update
on the entire original source space, including absent and post-overflow paths. -/
theorem bPlus_reflected_transition (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) :
    bPlus rate rewards C_star C_h u t a z =
      max (bMinus rate rewards C_star C_h u t a z +
        x rate rewards C_star C_h u t a z) 0 := by
  by_cases hE : z ∈ E u t
  · by_cases hG : z ∈ G rate rewards C_star C_h u t
    · obtain ⟨L, c, hL, hc, henabled, hbefore, hafter, _, _, hraw, _⟩ :=
        firstCell_actual_queue_readouts rate rewards C_star C_h u t a z hE
      have hstate := run_overflow_false_of_G rate rewards C_star C_h u t a z hG L hL
      have hrawEstimate : RecordedRoundMoments.rawEstimate q
          (RecordedQueueRun.run q L) c a =
            ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
              rate rewards C_star C_h u t a z := by
        change (RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord q (RecordedQueueRun.run q L) c a) : ℝ) /
            ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) = _
        exact hraw.symm
      have hretained :
          ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
              rate rewards C_star C_h u t a z =
            ReferenceFirstCollectionCurrentRawMoments.currentRaw
              rate rewards C_star C_h t a z := by
        simp [ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw, hG]
      have htransition := normalizedReadout_step_reflected rate
        (RecordedQueueRun.run q L) c a hstate henabled
      rw [bPlus, Set.indicator_of_mem hE, hafter,
        bMinus, Set.indicator_of_mem hE, hbefore,
        x, Set.indicator_of_mem hG]
      rw [htransition, hrawEstimate, hretained]
      apply congrArg (fun v : ℝ => max v 0)
      ring
    · obtain ⟨L, c, hL, hc, henabled, hbefore, hafter, _, _, _, _⟩ :=
        firstCell_actual_queue_readouts rate rewards C_star C_h u t a z hE
      have hstate : (RecordedQueueRun.run q L).overflow = true := by
        have hprefix : prefixReadout? rate rewards C_star C_h t z =
            some (stateReadout (RecordedQueueRun.run q L)) := by
          simp [ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hL]
        cases hs : (RecordedQueueRun.run q L).overflow with
        | false => exact False.elim (hG ⟨hE, ⟨_, hprefix, hs⟩⟩)
        | true => rfl
      have hpreserve := RecordedQueueRun.step_after_overflow_preserves
        q (RecordedQueueRun.run q L) c hstate a
      have htransition :
          normalizedReadoutBacklog rate (some (stateReadout
            (RecordedQueueRun.step q (RecordedQueueRun.run q L) c))) a =
          normalizedReadoutBacklog rate (some (stateReadout
            (RecordedQueueRun.run q L))) a := by
        simp [normalizedReadoutBacklog, stateReadout, hpreserve.1]
      have hnonneg := (bMinus_global_bounds rate rewards C_star C_h u t a z).1
      have hpreNonneg :
          0 ≤ normalizedReadoutBacklog rate
            (some (stateReadout (RecordedQueueRun.run q L))) a := by
        simpa [bMinus, Set.indicator_of_mem hE, hbefore] using hnonneg
      rw [bPlus, Set.indicator_of_mem hE, hafter,
        bMinus, Set.indicator_of_mem hE, hbefore,
        x, Set.indicator_of_notMem hG, htransition]
      simp [max_eq_left hpreNonneg]
  · have hG : z ∉ G rate rewards C_star C_h u t := by
      intro hz
      exact hE hz.1
    rw [bPlus, Set.indicator_of_notMem hE,
      bMinus, Set.indicator_of_notMem hE,
      x, Set.indicator_of_notMem hG]
    simp

theorem bPlus_measurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Measurable (bPlus rate rewards C_star C_h u t a) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hE : MeasurableSet (E u t) := hle _
    (ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t)
  have hpost := after?_measurable rate rewards C_star C_h control0 t
  have hproject : Measurable (fun r : Option (QueueReadout p.K) =>
      normalizedReadoutBacklog rate r a) := by
    classical
    exact measurable_of_countable _
  exact (hproject.comp hpost).indicator hE

theorem bMinus_measurable_ambient (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Measurable (bMinus rate rewards C_star C_h u t a) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  exact Measurable.mono
    (bMinus_measurable rate rewards C_star C_h control0 u t a) hle le_rfl

theorem x_measurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Measurable (x rate rewards C_star C_h u t a) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hG : MeasurableSet (G rate rewards C_star C_h u t) := hle _
    (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
      rate rewards C_star C_h control0 u t)
  have hindicator : Measurable (fun z : SourceInput p =>
      (G rate rewards C_star C_h u t).indicator (fun _ => (1 : ℝ)) z) :=
    measurable_const.indicator hG
  have hfun : x rate rewards C_star C_h u t a = fun z =>
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
          rate rewards C_star C_h u t a z -
        4 * (G rate rewards C_star C_h u t).indicator (fun _ => (1 : ℝ)) z := by
    funext z
    exact x_eq_retainedRaw_sub_service rate rewards C_star C_h u t a z
  rw [hfun]
  exact (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_measurable
      rate rewards C_star C_h control0 u t a).sub
    (measurable_const.mul hindicator)

private theorem integrable_of_bounded_measurable
    {f : SourceInput p → ℝ} (hf : Measurable f) (C : ℝ)
    (_hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C) :
    Integrable f (sourceInputLaw p) := by
  have hconst : Integrable (fun _ : SourceInput p => C) (sourceInputLaw p) :=
    integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  simpa [Real.norm_eq_abs, abs_of_nonneg _hC] using hbound z

private theorem square_norm_le_of_nonneg_le {v M : ℝ}
    (hv : 0 ≤ v) (hvm : v ≤ M) : ‖v ^ 2‖ ≤ M ^ 2 := by
  have hM : 0 ≤ M := le_trans hv hvm
  have hMv : 0 ≤ M - v := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg v)]
  nlinarith [mul_nonneg hv hMv, mul_nonneg hMv hM]

/-- The first before and after backlog scalars are integrable under the
original source law by their actual queue envelopes. -/
theorem bMinus_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (bMinus rate rewards C_star C_h u t a) (sourceInputLaw p) := by
  apply integrable_of_bounded_measurable
    (bMinus_measurable_ambient rate rewards C_star C_h control0 u t a)
    (2 * Bcap rate)
  · unfold Bcap
    positivity [rate.eta.property]
  · intro z
    have h := bMinus_global_bounds rate rewards C_star C_h u t a z
    rw [Real.norm_of_nonneg h.1]
    exact h.2

theorem bPlus_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (bPlus rate rewards C_star C_h u t a) (sourceInputLaw p) := by
  apply integrable_of_bounded_measurable
    (bPlus_measurable rate rewards C_star C_h control0 u t a)
    (2 * Bcap rate)
  · unfold Bcap
    positivity [rate.eta.property]
  · intro z
    have h := bPlus_global_bounds rate rewards C_star C_h u t a z
    rw [Real.norm_of_nonneg h.1]
    exact h.2

theorem bMinus_sq_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (fun z => (bMinus rate rewards C_star C_h u t a z) ^ 2)
      (sourceInputLaw p) := by
  have hm := (bMinus_measurable_ambient rate rewards C_star C_h control0 u t a).pow_const 2
  apply integrable_of_bounded_measurable hm ((2 * Bcap rate) ^ 2) (sq_nonneg _)
  intro z
  have h := bMinus_global_bounds rate rewards C_star C_h u t a z
  exact square_norm_le_of_nonneg_le h.1 h.2

theorem bPlus_sq_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (fun z => (bPlus rate rewards C_star C_h u t a z) ^ 2)
      (sourceInputLaw p) := by
  have hm := (bPlus_measurable rate rewards C_star C_h control0 u t a).pow_const 2
  apply integrable_of_bounded_measurable hm ((2 * Bcap rate) ^ 2) (sq_nonneg _)
  intro z
  have h := bPlus_global_bounds rate rewards C_star C_h u t a z
  exact square_norm_le_of_nonneg_le h.1 h.2

private theorem x_norm_bound (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) :
    ‖x rate rewards C_star C_h u t a z‖ ≤
      4 + 1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hC : 0 ≤ 4 + 1 / CanonicalRecordingRates.beta p rate.eta.val := by
    positivity [CanonicalRecordingRates.beta_pos p rate.eta.property]
  by_cases hz : z ∈ G rate rewards C_star C_h u t
  · rw [x, Set.indicator_of_mem hz, Real.norm_eq_abs]
    have hr := ReferenceFirstCollectionCurrentRawMoments.currentRaw_bounds_on_firstCell
      rate rewards C_star C_h u t a z hz.1
    apply abs_le.mpr
    constructor <;> nlinarith [hr.1, hr.2, hC]
  · rw [x, Set.indicator_of_notMem hz]
    simp
    positivity [CanonicalRecordingRates.beta_pos p rate.eta.property]

theorem x_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (x rate rewards C_star C_h u t a) (sourceInputLaw p) := by
  apply integrable_of_bounded_measurable
    (x_measurable rate rewards C_star C_h control0 u t a)
    (4 + 1 / CanonicalRecordingRates.beta p rate.eta.val)
  · positivity [CanonicalRecordingRates.beta_pos p rate.eta.property]
  · exact x_norm_bound rate rewards C_star C_h u t a

theorem bMinus_mul_x_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (fun z => bMinus rate rewards C_star C_h u t a z *
      x rate rewards C_star C_h u t a z) (sourceInputLaw p) := by
  have hm : Measurable (fun z => bMinus rate rewards C_star C_h u t a z *
      x rate rewards C_star C_h u t a z) :=
    (bMinus_measurable_ambient rate rewards C_star C_h control0 u t a).mul
      (x_measurable rate rewards C_star C_h control0 u t a)
  apply integrable_of_bounded_measurable hm
    ((2 * Bcap rate) * (4 + 1 / CanonicalRecordingRates.beta p rate.eta.val))
  · unfold Bcap
    positivity [rate.eta.property,
      CanonicalRecordingRates.beta_pos p rate.eta.property]
  · intro z
    rw [norm_mul]
    calc
      ‖bMinus rate rewards C_star C_h u t a z‖ *
          ‖x rate rewards C_star C_h u t a z‖ ≤
        (2 * Bcap rate) *
          (4 + 1 / CanonicalRecordingRates.beta p rate.eta.val) := by
            have hM : ‖bMinus rate rewards C_star C_h u t a z‖ ≤
                2 * Bcap rate := by
              have hb := bMinus_global_bounds rate rewards C_star C_h u t a z
              rw [Real.norm_of_nonneg hb.1]
              exact hb.2
            have hX := x_norm_bound rate rewards C_star C_h u t a z
            have hM0 : 0 ≤ 2 * Bcap rate := by
              unfold Bcap
              positivity [rate.eta.property]
            calc
              _ ≤ (2 * Bcap rate) *
                  ‖x rate rewards C_star C_h u t a z‖ :=
                mul_le_mul_of_nonneg_right hM (norm_nonneg _)
              _ ≤ (2 * Bcap rate) *
                  (4 + 1 / CanonicalRecordingRates.beta p rate.eta.val) :=
                mul_le_mul_of_nonneg_left hX hM0

end Bandits.Support.ReferenceFirstCollectionCurrentQueueReadout
