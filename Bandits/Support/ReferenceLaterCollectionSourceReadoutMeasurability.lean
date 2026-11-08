/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterCollectionReadoutDomain
public import Bandits.Support.ReferenceCompleteSuffixInputMeasurability

import Mathlib.MeasureTheory.Function.Floor

/-!
# Optional numerical observations at actual later-collection indices

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,355-408`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-75`.

The carrier is the existing genuine complete-suffix index subtype. The older
start varies independently of that index. The exact accepted guard supplies
the option domain, and the accepted jointly measurable recorder-call code
supplies the same selected payload, enabled bit and actual marker. The
factorization below is proved on both literal collection constructors before
using that code's Borel producer. In particular it does not specialize a
fixed-parameter recording-map theorem to varying weights.

Whole reward and rate vectors are retained. Arrivals use the original integer
scale and the literal floor, including gated zero; absent cells stay absent.
These internal results do not prove coverage, a list calendar, queue or score
truth, adaptation, an execution law, or any manuscript theorem. The next
consumer is `ReferenceLaterCollectionCalendarMeasurability`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceLaterCollectionSourceReadoutMeasurability

open ReferenceCompleteSuffixInputMeasurability

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The literal full numerical coordinates of an existing queue input. -/
def numericalCoordinates (c : RecordedQueueRun.RoundInput p.K) :
    Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ))) :=
  (c.enabled, (c.recordedArm, (c.reward, c.rate)))

/-- The enabled bit and every original quantized arrival. -/
def arrivalCoordinates (rate : ReferenceActivePhysicalStep.RateInput p)
    (c : RecordedQueueRun.RoundInput p.K) : Bool × (Fin p.K → ℕ) :=
  (c.enabled, fun a => RecordedQueueRun.quantizedArrival
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)

/-- A projection of the accepted actual call observation. No call remains
absent, while an absent recorder output remains an absent marker inside the
present call. This definition does not execute or replace the recorder. -/
def numericalFromRecordCode
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate))
    (reward : Fin p.K → ℝ) :
    Option (Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ)))) :=
  (ReferenceCoordinatorRecorderCallTrace.cell code).map fun entry =>
    (entry.2.2.1, ((entry.2.2.2).bind (fun out => out.gateArm),
      (reward, entry.1.1.payload.rate)))

/-- Exact value factorization for every actual record. The two admitted
constructors use their actual collection recorder, even if a later operation
fails. The test is the actual option domain, with no off-domain numeric value. -/
theorem readout_numerical_factorization (s : ℕ)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record).map
        numericalCoordinates =
      if (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record).isSome = true then
        numericalFromRecordCode (ReferenceActiveHorizonMeasurability.roundRecordCode record)
          (fun a => ((record.input.rewards record.input.time a).val : ℝ) / (D p : ℝ))
      else none := by
  classical
  by_cases hsome :
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record).isSome = true
  · have hguard :=
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain s record).mp hsome
    cases hreadout : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record with
    | none => simp only [hreadout, Option.isSome_none, Bool.false_eq_true] at hsome
    | some c =>
        obtain ⟨payload, ledger, started, weights, out, hcall, _htail, _hrun,
          _henabled, hclock, hrate, hreward, hdiag, hgate, _harr⟩ :=
          ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call s record c hreadout
        have hprepared :
            record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
          rw [record.output_eq]
          rfl
        have hselection : ReferenceCoordinatorRecorderCallTrace.selection
            (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
              record.output.preparation.coordinator.selection.map
                ReferenceLiveDispatchOutputMeasurability.encodeSelection := by
          calc
            _ = (ReferenceActivePhysicalStep.dispatch record.input).selection.map
                ReferenceLiveDispatchOutputMeasurability.encodeSelection :=
              (ReferenceActiveHorizonMeasurability.roundRecordCode_front record).1
            _ = _ := by rw [hprepared]; rfl
        simp only [Option.isSome_some, ite_true, Option.map_some]
        cases hcoord : record.output.preparation.coordinator with
        | first outcome => simp only [hcoord, and_false] at hguard
        | invalidCollectionCutoff => simp only [hcoord, and_false] at hguard
        | dagger => simp only [hcoord, and_false] at hguard
        | live registers owned base outcome =>
            cases outcome with
            | cutoffChosen dispatched hstart newLedger hinit hcand hdomainCut hclockLive
                hpending hnone selected =>
                have hlater : s < registers.payload.sigma.val := by
                  simpa only [hcoord] using hguard.2
                have hcallFields :
                    (⟨payload, (ledger, (started, weights))⟩ :
                      Σ payload : ReferenceActivePhysicalStep.Payload rate,
                        ReferenceActivePhysicalStep.Ledger rate ×
                          CoordinatorPhaseClock.StartRoundResult p ×
                            (CanonicalFastSampling.FastArm payload.slowSet → ℝ)) =
                      ⟨registers.payload,
                        (ReferenceActivePhysicalStep.sharedLedger newLedger,
                          (dispatched.startResult,
                            (ReferenceActivePhysicalStep.liveRegistersAt registers
                              record.input.time).complementWeights))⟩ := by
                  apply Option.some.inj
                  simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall,
                    ite_eq_left hguard.1, hcoord,
                    ite_eq_left hlater] using hcall.symm
                cases hcallFields
                unfold numericalFromRecordCode ReferenceCoordinatorRecorderCallTrace.cell
                rw [hselection, ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics
                  record, hdiag]
                simp only [hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.selectionAt, dite_true,
                  ReferenceLiveDispatchOutputMeasurability.encodeSelection, Option.map_some,
                  Option.bind_some, hgate]
                simp only [ReferenceCoordinatorRecorderCallTrace.enabled_eq_time_before_startGrid,
                  ReferenceActiveHorizonMeasurability.roundRecordCode,
                  numericalCoordinates, hclock, hrate, hreward]
            | _ => simp only [hcoord, and_false] at hguard
        | collection payload₀ ledger₀ clock cutoff outcome =>
            cases outcome with
            | continuing core snapshot boundary scores =>
                have hcallFields :
                    (⟨payload, (ledger, (started, weights))⟩ :
                      Σ payload : ReferenceActivePhysicalStep.Payload rate,
                        ReferenceActivePhysicalStep.Ledger rate ×
                          CoordinatorPhaseClock.StartRoundResult p ×
                            (CanonicalFastSampling.FastArm payload.slowSet → ℝ)) =
                      ⟨payload₀, (ledger₀, (snapshot.clockStarted,
                        CoordinatorCollectionInteractive.PreObservationInputs.weights
                          (ReferenceActivePhysicalStep.collectionInput record.input payload₀
                            ledger₀ clock cutoff)
                          snapshot.inputsValid.ledger_valid
                          snapshot.inputsValid.assignment_eq))⟩ := by
                  apply Option.some.inj
                  simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall,
                    ite_eq_left hguard.1, hcoord]
                    using hcall.symm
                cases hcallFields
                unfold numericalFromRecordCode ReferenceCoordinatorRecorderCallTrace.cell
                rw [hselection, ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics
                  record, hdiag]
                simp only [hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceLiveDispatchOutputMeasurability.encodeSelection, Option.map_some,
                  Option.bind_some, hgate]
                simp only [ReferenceCoordinatorRecorderCallTrace.enabled_eq_time_before_startGrid,
                  ReferenceActiveHorizonMeasurability.roundRecordCode,
                  numericalCoordinates, hclock, hrate, hreward]
            | _ => simp only [hcoord, and_false] at hguard
  · have hnone : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = none := by
      cases h : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record with
      | none => rfl
      | some c => exact False.elim (hsome (by rw [h]; rfl))
    rw [ite_eq_right hsome, hnone, Option.map_none]

private theorem measurable_numericalFromRecordCode : Measurable
    (fun z : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) ×
      (Fin p.K → ℝ) => numericalFromRecordCode z.1 z.2) := by
  let Entry := ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
    (Bool × (Bool × Option (CoordinatorRecordingOperation.Output p)))
  have hpayload : Measurable (fun entry : Entry => entry.1.1.payload) := by
    have hview : Measurable
        (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
          (p := p) (rate := rate)) := comap_measurable _
    exact measurable_fst.comp (hview.comp (measurable_fst.comp measurable_fst))
  have hrate : Measurable (fun entry : Entry => entry.1.1.payload.rate) :=
    AssignmentPayloadDerivedMeasurability.measurable_inputRate.comp hpayload
  have hmarker : Measurable (fun entry : Entry =>
      (entry.2.2.2).bind (fun out => out.gateArm)) := by
    have hgate : Measurable (fun output : Option (CoordinatorRecordingOperation.Output p) =>
        output.bind (fun out => out.gateArm)) := Measurable.of_discrete
    exact hgate.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp measurable_id)))
  have hentry : Measurable (fun z : Entry ×
      (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) ×
        (Fin p.K → ℝ)) =>
      (z.1.2.2.1, ((z.1.2.2.2).bind (fun out => out.gateArm),
        (z.2.2, z.1.1.1.payload.rate)))) :=
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
      ((hmarker.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_snd).prodMk (hrate.comp measurable_fst)))
  exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    _ hentry (fun z => ReferenceCoordinatorRecorderCallTrace.cell z.1)
    (ReferenceCoordinatorRecorderCallTrace.measurable_cell.comp measurable_fst)

/-- The literal arrival arithmetic on numerical coordinates. Its zero branch
is the existing nonmarker arrival, and does not fill an absent readout. -/
def arrivalsFromNumerical (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ)))) :
    Bool × (Fin p.K → ℕ) :=
  (z.1, fun a => if z.2.1 = some a then
    Nat.floor (((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) *
      z.2.2.1 a / z.2.2.2 a) else 0)

/-- The arithmetic projection retains the same enabled bit and every arm. -/
theorem arrivalsFromNumerical_numericalCoordinates
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (c : RecordedQueueRun.RoundInput p.K) :
    arrivalsFromNumerical rate (numericalCoordinates c) = arrivalCoordinates rate c := rfl

/-- Joint Borelness of full-vector division and floor on the natural product
space. Positivity is already a field of actual cells, not an extra premise. -/
theorem measurable_arrivalsFromNumerical (rate : ReferenceActivePhysicalStep.RateInput p) :
    Measurable (arrivalsFromNumerical rate) := by
  classical
  apply measurable_fst.prodMk
  apply Measurable.of_eval
  intro a
  have hmarker : Measurable (fun z :
      Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ))) => z.2.1) :=
    measurable_fst.comp measurable_snd
  have hreward : Measurable (fun z :
      Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ))) => z.2.2.1 a) :=
    (measurable_pi_apply a).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hrate : Measurable (fun z :
      Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ))) => z.2.2.2 a) :=
    (measurable_pi_apply a).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  exact Measurable.ite (hmarker.eq_const (some a)).setOf
    (Nat.measurable_floor.comp ((measurable_const.mul hreward).div hrate)) measurable_const

section Indexed

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) (k : ℕ)

/-- The exact existing optional readout at one genuine suffix index. The
first argument is the older assignment start, independently of source time. -/
def actualReadout (q : ℕ × IndexedSource rate rewards C_star C_h k) :
    Option (RecordedQueueRun.RoundInput p.K) :=
  ReferenceLaterCollectionArrivalReadout.laterCollectionReadout q.1
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate q.2.val rewards C_star C_h).get ⟨k, q.2.property⟩)

/-- The accepted unconditional record guard, composed with the actual input. -/
theorem actualReadout_isSome_iff
    (q : ℕ × IndexedSource rate rewards C_star C_h k) :
    (actualReadout rate rewards C_star C_h k q).isSome = true ↔
      ReferenceLaterCollectionReadoutDomain.observableReadoutGuard rate q.1
        (actualRoundInputAt rate rewards C_star C_h k q.2) :=
  ReferenceLaterCollectionReadoutDomain.readout_isSome_iff rate q.1 _

/-- Joint Borelness of the exact domain, using countably many older-start
slices. No successful-tail or supplied domain-measurability premise occurs. -/
theorem measurableSet_actualReadout_isSome : MeasurableSet
    {q : ℕ × IndexedSource rate rewards C_star C_h k |
      (actualReadout rate rewards C_star C_h k q).isSome = true} := by
  have hguard : Measurable (fun q : ℕ × IndexedSource rate rewards C_star C_h k =>
      ReferenceLaterCollectionReadoutDomain.observableReadoutGuard rate q.1
        (actualRoundInputAt rate rewards C_star C_h k q.2)) := by
    apply measurable_from_prod_countable_right
    intro s
    exact measurableSet_setOfPred.mp
      ((ReferenceLaterCollectionReadoutDomain.measurableSet_observableReadoutGuard rate s).preimage
      (measurable_actualRoundInputAt rate rewards C_star C_h k))
  have heq : {q : ℕ × IndexedSource rate rewards C_star C_h k |
      (actualReadout rate rewards C_star C_h k q).isSome = true} =
      {q | ReferenceLaterCollectionReadoutDomain.observableReadoutGuard rate q.1
        (actualRoundInputAt rate rewards C_star C_h k q.2)} := by
    ext q
    exact actualReadout_isSome_iff rate rewards C_star C_h k q
  rw [heq]
  exact hguard.setOf

/-- The entire optional numerical tuple is jointly Borel on the original
source subtype and arbitrary older start. Disabled collection stays present. -/
theorem measurable_actualReadout_numerical : Measurable
    (fun q : ℕ × IndexedSource rate rewards C_star C_h k =>
      (actualReadout rate rewards C_star C_h k q).map numericalCoordinates) := by
  have hinput := measurable_actualRoundInputAt rate rewards C_star C_h k
  have htime := ReferenceActivePhysicalStepMeasurability.measurable_time.comp hinput
  have hreward : Measurable (fun x : IndexedSource rate rewards C_star C_h k =>
      fun a => (((actualRoundInputAt rate rewards C_star C_h k x).rewards
        (actualRoundInputAt rate rewards C_star C_h k x).time a).val : ℝ) / (D p : ℝ)) := by
    have heq : (fun x : IndexedSource rate rewards C_star C_h k => fun a =>
        (((actualRoundInputAt rate rewards C_star C_h k x).rewards
          (actualRoundInputAt rate rewards C_star C_h k x).time a).val : ℝ) / (D p : ℝ)) =
        (fun x => fun a => ((rewards
          (actualRoundInputAt rate rewards C_star C_h k x).time a).val : ℝ) / (D p : ℝ)) := by
      funext x a
      rw [(actualRoundInputAt_fields rate rewards C_star C_h k x).2.2.1]
    rw [heq]
    exact (measurable_of_countable (fun t : Fin p.T =>
      fun a : Fin p.K => ((rewards t a).val : ℝ) / (D p : ℝ))).comp htime
  have hvalues : Measurable (fun q : ℕ × IndexedSource rate rewards C_star C_h k =>
      numericalFromRecordCode (actualRecordCodeAt rate rewards C_star C_h k q.2)
        (fun a => (((actualRoundInputAt rate rewards C_star C_h k q.2).rewards
          (actualRoundInputAt rate rewards C_star C_h k q.2).time a).val : ℝ) / (D p : ℝ))) :=
    measurable_numericalFromRecordCode.comp
      (((measurable_actualRecordCodeAt rate rewards C_star C_h k).comp measurable_snd).prodMk
        (hreward.comp measurable_snd))
  unfold actualReadout
  simp_rw [readout_numerical_factorization]
  exact Measurable.ite
    (measurableSet_actualReadout_isSome rate rewards C_star C_h k) hvalues measurable_const

/-- Joint Borelness of the complete optional arrival vector. The outer
option is exactly the same as that of the original numerical readout. -/
theorem measurable_actualReadout_arrivals : Measurable
    (fun q : ℕ × IndexedSource rate rewards C_star C_h k =>
      (actualReadout rate rewards C_star C_h k q).map (arrivalCoordinates rate)) := by
  have hsome : Measurable (fun z :
      Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ))) =>
      (some (arrivalsFromNumerical rate z) : Option (Bool × (Fin p.K → ℕ)))) :=
    (measurable_of_countable (some : (Bool × (Fin p.K → ℕ)) →
      Option (Bool × (Fin p.K → ℕ)))).comp (measurable_arrivalsFromNumerical rate)
  -- This uses the existing canonical option elimination on the continuous
  -- numerical input and the existing countable option space on the output.
  have h := (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim none
    (fun z => some (arrivalsFromNumerical rate z)) hsome).comp
      (measurable_actualReadout_numerical rate rewards C_star C_h k)
  convert h using 1
  funext q
  dsimp only [Function.comp_def]
  cases actualReadout rate rewards C_star C_h k q <;> rfl

/-- The actual physical-start pair is Borel on the same genuine subtype. -/
theorem measurable_physicalStart_pair : Measurable
    (fun x : IndexedSource
      rate rewards C_star C_h k =>
      (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h, x)) :=
  ((measurable_physicalStart
    rate rewards C_star C_h).comp measurable_subtype_coe).prodMk measurable_id

/-- Optional numerical measurability at the actual source-generated older
start, with no additional launch, ordinary or successful-readout premise. -/
theorem measurable_physicalStartReadout_numerical : Measurable
    (fun x : IndexedSource
      rate rewards C_star C_h k =>
      (actualReadout rate rewards C_star C_h k
        (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h, x)).map
          numericalCoordinates) :=
  (measurable_actualReadout_numerical rate rewards C_star C_h k).comp
    (measurable_physicalStart_pair rate rewards C_star C_h k)

/-- Optional full arrival-vector measurability at that same physical start. -/
theorem measurable_physicalStartReadout_arrivals : Measurable
    (fun x : IndexedSource
      rate rewards C_star C_h k =>
      (actualReadout rate rewards C_star C_h k
        (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h, x)).map
          (arrivalCoordinates rate)) :=
  (measurable_actualReadout_arrivals rate rewards C_star C_h k).comp
    (measurable_physicalStart_pair rate rewards C_star C_h k)

/-- A true readout retains the whole original reward table at its actual
time. This equality uses no successful-tail assumption. -/
theorem actualReadout_reward
    (q : ℕ × IndexedSource
      rate rewards C_star C_h k)
    (c : RecordedQueueRun.RoundInput p.K)
    (hreadout : actualReadout rate rewards C_star C_h k q = some c) :
    c.reward = fun a => ((rewards
      (actualRoundInputAt
        rate rewards C_star C_h k q.2).time a).val : ℝ) / (D p : ℝ) := by
  obtain ⟨payload, ledger, started, weights, out, _hcall, _htail, _hrun,
    _henabled, _hclock, _hrate, hreward, _hdiag, _hgate, _harr⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call q.1 _ c hreadout
  change c.reward = (fun a =>
    (((actualRoundInputAt
      rate rewards C_star C_h k q.2).rewards
      (actualRoundInputAt
        rate rewards C_star C_h k q.2).time a).val : ℝ) / (D p : ℝ)) at hreward
  rw [(actualRoundInputAt_fields
    rate rewards C_star C_h k q.2).2.2.1] at hreward
  exact hreward

/-- Literal fields of the same computed cell and the same actual collection
call. The only logical input is equality to that existing optional readout.
Both collection enable comparisons and the original full rate vector are
conclusions; no marker or value measurability is assumed. -/
theorem actualReadout_call_fields
    (q : ℕ × IndexedSource
      rate rewards C_star C_h k)
    (c : RecordedQueueRun.RoundInput p.K)
    (hreadout : actualReadout rate rewards C_star C_h k q = some c) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate q.2.val rewards C_star C_h).get ⟨k, q.2.property⟩
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
      (out : CoordinatorRecordingOperation.Output p),
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall q.1 record =
        some ⟨payload, ledger, started, weights⟩ ∧
      numericalCoordinates c =
        (ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time,
          (out.gateArm, ((fun a => ((rewards record.input.time a).val : ℝ) / (D p : ℝ)),
            payload.rate))) ∧
      ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time =
        decide (record.input.time.val + 1 < started.clock.g) ∧
      ReferenceCoordinatorRecorderCallTrace.recording
        (actualRecordCodeAt
          rate rewards C_star C_h k q.2) = some out := by
  obtain ⟨payload, ledger, started, weights, out, hcall, _htail, _hrun,
    henabled, hclock, hrate, _hreward, hdiag, hgate, _harr⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call q.1 _ c hreadout
  refine ⟨payload, ledger, started, weights, out, hcall, ?_, henabled.symm.trans hclock, ?_⟩
  · unfold numericalCoordinates
    rw [henabled, ← hgate, hrate, actualReadout_reward rate rewards C_star C_h k q c hreadout]
    rfl
  · exact (ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics _).trans hdiag

/-- The same computed cell has the original source floor on its actual
marker fibres, including zero rewards, for every older-start argument. -/
theorem actualReadout_arrival_formula
    (q : ℕ × IndexedSource
      rate rewards C_star C_h k)
    (c : RecordedQueueRun.RoundInput p.K)
    (hreadout : actualReadout rate rewards C_star C_h k q = some c) (a : Fin p.K) :
    RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a =
      if c.recordedArm = some a then Nat.floor ((D p : ℝ) * rate.eta.val *
        (((rewards (actualRoundInputAt
          rate rewards C_star C_h k q.2).time a).val : ℝ) / (D p : ℝ)) / c.rate a)
      else 0 := by
  classical
  unfold RecordedQueueRun.quantizedArrival
  rw [actualReadout_reward rate rewards C_star C_h k q c hreadout,
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_eq_eta_mul_D]
  congr 1
  congr 1
  change rate.eta.val * (D p : ℝ) * _ / _ = (D p : ℝ) * rate.eta.val * _ / _
  ring

/-- At the physical start the source identification is also the accepted
collection-arrival theorem applied to this very indexed record. -/
theorem physicalStartReadout_arrival_formula
    (x : IndexedSource
      rate rewards C_star C_h k)
    (c : RecordedQueueRun.RoundInput p.K)
    (hreadout : actualReadout rate rewards C_star C_h k
      (ReferenceCompletePhysicalHistory.physicalStart
        rate x.val rewards C_star C_h, x) = some c) :
    ∀ a, RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a =
      if c.recordedArm = some a then Nat.floor ((D p : ℝ) * rate.eta.val *
        (((rewards (actualRoundInputAt
          rate rewards C_star C_h k x).time a).val : ℝ) / (D p : ℝ)) / c.rate a)
      else 0 :=
  ReferenceLaterCollectionArrivalReadout.sourceIndexedReadout_arrival_formula
    rate rewards C_star C_h x.val ⟨k, x.property⟩ c hreadout

end Indexed

end Bandits.Support.ReferenceLaterCollectionSourceReadoutMeasurability

end
