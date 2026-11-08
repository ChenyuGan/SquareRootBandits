/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLiveRecorderJointMeasurability
public import Bandits.Support.ReferenceLiveServiceTailMeasurability

/-!
# Joint measurability of the composed live post-choice tail

Sources: `sources/zip4/manuscript/06_interruptions.tex:256-296` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-60`.

The local input varies the original payload, canonical live discrete code,
retained start result, complete UP decoder bank, physical time, whole
continuous row, own arm, and own grid observation independently. The actual
recorder result is computed from the accepted recorder producer and supplied
to the accepted source-ordered service, confirmation, and finish suffix. The
output uses that suffix's whole-observation code. Every failure and successful
recorder value is retained; no run-validity or success premise is supplied.

This module proves an internal local composition and its same-input identity.
It does not assert dispatch, a full physical step, a horizon result, or
manuscript/regret closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceActiveLiveTailMeasurability

variable {p : Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

local instance liveTailCoordinatorFailureMeasurableSpace :
    MeasurableSpace ReferenceActivePhysicalStep.CoordinatorFailure := ⊤

/-- The literal product of the primitive inputs read by the local live
post-choice computation. The discrete registers are the accepted canonical
`LiveDiscrete` code, and the row remains the complete continuous row. -/
abbrev LivePostChoiceCoordinates (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalStep.Payload rate ×
    (ReferenceActivePhysicalStepMeasurability.LiveDiscrete p ×
      (CoordinatorPhaseClock.StartRoundResult p ×
        (CoordinatorUpReception.UpDecoderBank p ×
          (Fin p.T ×
            (CompletePublicTable.CompleteRow p ×
              (Fin p.K × Fin (D p + 1)))))))

def localPayload (z : LivePostChoiceCoordinates p rate) := z.1

def localLiveCode (z : LivePostChoiceCoordinates p rate) := z.2.1

def localStarted (z : LivePostChoiceCoordinates p rate) := z.2.2.1

def localIncomingBank (z : LivePostChoiceCoordinates p rate) := z.2.2.2.1

def localTime (z : LivePostChoiceCoordinates p rate) := z.2.2.2.2.1

def localRow (z : LivePostChoiceCoordinates p rate) := z.2.2.2.2.2.1

def localOwnArm (z : LivePostChoiceCoordinates p rate) := z.2.2.2.2.2.2.1

def localGridObservation (z : LivePostChoiceCoordinates p rate) :=
  z.2.2.2.2.2.2.2

theorem measurable_localPayload :
    Measurable (localPayload (p := p) (rate := rate)) := measurable_fst

theorem measurable_localLiveCode :
    Measurable (localLiveCode (p := p) (rate := rate)) :=
  measurable_fst.comp measurable_snd

theorem measurable_localStarted :
    Measurable (localStarted (p := p) (rate := rate)) :=
  measurable_fst.comp (measurable_snd.comp measurable_snd)

theorem measurable_localIncomingBank :
    Measurable (localIncomingBank (p := p) (rate := rate)) :=
  measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp measurable_snd))

theorem measurable_localTime :
    Measurable (localTime (p := p) (rate := rate)) :=
  measurable_fst.comp
    (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))

theorem measurable_localRow :
    Measurable (localRow (p := p) (rate := rate)) :=
  measurable_fst.comp
    (measurable_snd.comp
      (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))

theorem measurable_localOwnArm :
    Measurable (localOwnArm (p := p) (rate := rate)) :=
  measurable_fst.comp
    (measurable_snd.comp
      (measurable_snd.comp
        (measurable_snd.comp
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))))

theorem measurable_localGridObservation :
    Measurable (localGridObservation (p := p) (rate := rate)) :=
  measurable_snd.comp
    (measurable_snd.comp
      (measurable_snd.comp
        (measurable_snd.comp
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))))

/-- Reuse the recorder producer's exact local coordinates. -/
def recorderCoordinates (z : LivePostChoiceCoordinates p rate) :
    ReferenceLiveRecorderJointMeasurability.RecorderCoordinates p rate :=
  (localPayload z,
    (localLiveCode z,
      (localStarted z,
        (localTime z,
          (localRow z, (localOwnArm z, localGridObservation z))))))

/-- The actual lossless recorder result, computed from these same primitive
inputs. It is not an independent composition premise. -/
def recorderCode (z : LivePostChoiceCoordinates p rate) :
    Option (ReferenceLiveServiceTailMeasurability.RecorderCode p) :=
  ReferenceLiveRecorderJointMeasurability.runCode (recorderCoordinates z)

/-- Assemble the accepted service-tail coordinates with the computed
recorder result, retaining the original payload and full row. -/
def liveServiceTailCoordinates (z : LivePostChoiceCoordinates p rate) :
    ReferenceLiveServiceTailMeasurability.LiveServiceTailCoordinates p rate :=
  ReferenceLiveServiceTailMeasurability.assembleLiveServiceTailCoordinates
    localLiveCode localStarted localIncomingBank localTime localGridObservation
    recorderCode localPayload localRow z

/-- The literal observation obtained by running the actual recorder followed
by the accepted service, confirmation, and finish implementation. -/
def livePostChoiceObservation (z : LivePostChoiceCoordinates p rate) :
    ReferenceActivePhysicalStep.CoordinatorObservation p rate :=
  ReferenceLiveServiceTailMeasurability.liveServiceTailObservation
    (liveServiceTailCoordinates z)

/-- The whole canonical observation code of the composed live tail. -/
def livePostChoiceWholeCode (z : LivePostChoiceCoordinates p rate) :
    ReferenceLiveServiceTailMeasurability.LiveServiceTailWholeCode p rate :=
  ReferenceLiveServiceTailMeasurability.liveServiceTailWholeCode
    (liveServiceTailCoordinates z)

/-- The accepted whole-code decoder recovers this same local computation,
including the complete failure, recorder, bank, and absent-UP fields. -/
theorem decode_livePostChoiceWholeCode
    (z : LivePostChoiceCoordinates p rate) :
    ReferenceLiveServiceTailMeasurability.decodeLiveServiceTailWholeObservation
      (livePostChoiceWholeCode z) = livePostChoiceObservation z := by
  exact ReferenceLiveServiceTailMeasurability.decode_liveServiceTailWholeCode
    (liveServiceTailCoordinates z)

/-- Joint measurability of the actual composed output on the full local
product. The recorder map is measured by its producer theorem, then fed to
the accepted whole-code service-tail composition. -/
theorem measurable_livePostChoiceWholeCode :
    Measurable (livePostChoiceWholeCode (p := p) (rate := rate)) := by
  have hrecorder : Measurable (recorderCode (p := p) (rate := rate)) := by
    change Measurable (fun z : LivePostChoiceCoordinates p rate =>
      ReferenceLiveRecorderJointMeasurability.runCode
        (localPayload z, (localLiveCode z, (localStarted z,
          (localTime z, (localRow z, (localOwnArm z, localGridObservation z)))))))
    exact ReferenceLiveRecorderJointMeasurability.measurable_runCode_comp
      localPayload localLiveCode localStarted localTime localRow localOwnArm
      localGridObservation
      measurable_localPayload measurable_localLiveCode measurable_localStarted
      measurable_localTime measurable_localRow measurable_localOwnArm
      measurable_localGridObservation
  change Measurable (fun z : LivePostChoiceCoordinates p rate =>
    ReferenceLiveServiceTailMeasurability.liveServiceTailWholeCode
      (ReferenceLiveServiceTailMeasurability.assembleLiveServiceTailCoordinates
        localLiveCode localStarted localIncomingBank localTime localGridObservation
        recorderCode localPayload localRow z))
  exact ReferenceLiveServiceTailMeasurability.measurable_liveServiceTailWholeCode_comp
    localLiveCode localStarted localIncomingBank localTime localGridObservation
    recorderCode localPayload localRow
    measurable_localLiveCode measurable_localStarted measurable_localIncomingBank
    measurable_localTime measurable_localGridObservation hrecorder
    measurable_localPayload measurable_localRow

/-- Compose the full local output from separately measurable primitive maps.
The recorder code is computed internally from the same payload, live code,
start result, time, whole row, own arm, and grid observation. -/
theorem measurable_livePostChoiceWholeCode_comp {Ω : Type*} [MeasurableSpace Ω]
    (payload : Ω → ReferenceActivePhysicalStep.Payload rate)
    (live : Ω → ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (started : Ω → CoordinatorPhaseClock.StartRoundResult p)
    (bank : Ω → CoordinatorUpReception.UpDecoderBank p)
    (time : Ω → Fin p.T)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (ownArm : Ω → Fin p.K) (observation : Ω → Fin (D p + 1))
    (hpayload : Measurable payload) (hlive : Measurable live)
    (hstarted : Measurable started) (hbank : Measurable bank)
    (htime : Measurable time) (hrow : Measurable row)
    (harm : Measurable ownArm) (hobservation : Measurable observation) :
    Measurable (fun ω => livePostChoiceWholeCode
      (payload ω, (live ω, (started ω, (bank ω,
        (time ω, (row ω, (ownArm ω, observation ω)))))))) := by
  have hrecorder : Measurable (fun ω =>
      ReferenceLiveRecorderJointMeasurability.runCode
        (payload ω, (live ω, (started ω,
          (time ω, (row ω, (ownArm ω, observation ω))))))) :=
    ReferenceLiveRecorderJointMeasurability.measurable_runCode_comp
      payload live started time row ownArm observation
      hpayload hlive hstarted htime hrow harm hobservation
  change Measurable (fun ω =>
    ReferenceLiveServiceTailMeasurability.liveServiceTailWholeCode
      (ReferenceLiveServiceTailMeasurability.assembleLiveServiceTailCoordinates
        live started bank time observation
        (fun ω => ReferenceLiveRecorderJointMeasurability.runCode
          (payload ω, (live ω, (started ω,
            (time ω, (row ω, (ownArm ω, observation ω)))))))
        payload row ω))
  exact ReferenceLiveServiceTailMeasurability.measurable_liveServiceTailWholeCode_comp
    live started bank time observation
    (fun ω => ReferenceLiveRecorderJointMeasurability.runCode
      (payload ω, (live ω, (started ω,
        (time ω, (row ω, (ownArm ω, observation ω)))))))
    payload row hlive hstarted hbank htime hobservation hrecorder hpayload hrow

/-- The exact source coordinates for every original physical input and its
prepared post-choice observation. This uses the accepted `coordinatesOf`
encoder and keeps the same original row, time, UP bank, payload, and start. -/
def coordinatesOf {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    LivePostChoiceCoordinates p rate :=
  let c := ReferenceLiveRecorderJointMeasurability.coordinatesOf
    prepared r q base started
  (c.1, (c.2.1, (c.2.2.1, (x.state.upDecoderBank,
    (c.2.2.2.1, (c.2.2.2.2.1, (c.2.2.2.2.2.1, c.2.2.2.2.2.2)))))))

/-- Expanding the product coordinates recovers precisely the accepted
canonical live encoding and the physical fields from the original input. -/
theorem coordinatesOf_eq
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    coordinatesOf prepared r q base started =
      (r.payload,
        (ReferenceActivePhysicalStepMeasurability.encodeLive r q base,
          (started,
            (x.state.upDecoderBank,
              (x.time,
                (x.row,
                  (prepared.coordinator.arm, prepared.coordinatorObservation))))))) := by
  simp [coordinatesOf, ReferenceLiveRecorderJointMeasurability.coordinatesOf]

/-- The composed recorder code is exactly the encoding of the accepted
recorder run at the same original input. Its identity is derived from the
producer's decode and coordinate-reconstruction theorems. -/
theorem recorderCode_coordinatesOf
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    recorderCode (coordinatesOf prepared r q base started) =
      CoordinatorRecordingMeasurability.encodeResult
        (CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.liveRecordingInput prepared r started)) := by
  have hdecoded := ReferenceLiveRecorderJointMeasurability.decodeResult_runCode
    (ReferenceLiveRecorderJointMeasurability.coordinatesOf prepared r q base started)
  rw [ReferenceLiveRecorderJointMeasurability.recordingInput_coordinatesOf]
    at hdecoded
  calc
    recorderCode (coordinatesOf prepared r q base started) =
        CoordinatorRecordingMeasurability.encodeResult
          (CoordinatorRecordingMeasurability.decodeResult
            (recorderCode (coordinatesOf prepared r q base started))) := by
      simp [recorderCode, recorderCoordinates, coordinatesOf,
        ReferenceLiveRecorderJointMeasurability.coordinatesOf,
        ReferenceLiveRecorderJointMeasurability.runCode,
        CoordinatorRecordingMeasurability.decodeResult_encodeResult]
    _ = CoordinatorRecordingMeasurability.encodeResult
          (CoordinatorRecorderComplementBridge.run
            (ReferenceActivePhysicalStep.liveRecordingInput prepared r started)) := by
      apply congrArg CoordinatorRecordingMeasurability.encodeResult
      change CoordinatorRecordingMeasurability.decodeResult
          (ReferenceLiveRecorderJointMeasurability.runCode
            (ReferenceLiveRecorderJointMeasurability.coordinatesOf
              prepared r q base started)) = _
      exact hdecoded

/-- The assembled suffix coordinates are exactly the accepted actual
coordinates once the recorder code has been computed. -/
theorem liveServiceTailCoordinates_coordinatesOf
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    liveServiceTailCoordinates (coordinatesOf prepared r q base started) =
      ReferenceLiveServiceTailMeasurability.actualLiveServiceTailCoordinates
        prepared r q base started := by
  change ((ReferenceActivePhysicalStepMeasurability.encodeLive r q base,
      (started, (x.state.upDecoderBank,
        (x.time, (prepared.coordinatorObservation,
          recorderCode (coordinatesOf prepared r q base started)))))),
      (r.payload, x.row)) =
    ((ReferenceActivePhysicalStepMeasurability.encodeLive r q base,
      (started, (x.state.upDecoderBank,
        (x.time, (prepared.coordinatorObservation,
          CoordinatorRecordingMeasurability.encodeResult
            (CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.liveRecordingInput prepared r started))))))),
      (r.payload, x.row))
  rw [recorderCode_coordinatesOf]

/-- Exact same-input reconstruction of the whole local output for every
original physical round and retained start result. No success, validity,
overflow, or reachability condition is assumed. -/
theorem livePostChoiceWholeCode_reconstructs_actual
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    ReferenceLiveServiceTailMeasurability.decodeLiveServiceTailWholeObservation
      (livePostChoiceWholeCode (coordinatesOf prepared r q base started)) =
        ReferenceActivePhysicalStep.livePostChoice prepared r q base started := by
  change ReferenceLiveServiceTailMeasurability.decodeLiveServiceTailWholeObservation
    (ReferenceLiveServiceTailMeasurability.liveServiceTailWholeCode
      (liveServiceTailCoordinates (coordinatesOf prepared r q base started))) = _
  rw [liveServiceTailCoordinates_coordinatesOf]
  exact ReferenceLiveServiceTailMeasurability.liveServiceTailWholeCode_reconstructs_actual
    prepared r q base started

end Bandits.Support.ReferenceActiveLiveTailMeasurability

end
