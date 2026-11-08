/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStepMeasurability

import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Canonical coordinates for the actual live pre-choice dispatcher

Sources: `sources/zip4/manuscript/06_interruptions.tex:235-296` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-60`.

This module sets up the existing live dispatcher's full carried payload,
lossless discrete register code, actual round time, and complete current row.
The live register time is reindexed by the actual round time exactly as in the
canonical physical step. It proves lossless coordinate decoding and exact
pointwise reconstruction of the canonical live call. Joint measurability of
the dispatcher output remains to be established; nothing here closes a
manuscript theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceLiveDispatchMeasurability

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

open ReferenceActivePhysicalStepMeasurability

/-- The complete local data read by the actual LIVE pre-choice dispatcher.
The original carried register time remains in `LiveDiscrete`; `roundTime` is
the actual active-round time written by `liveRegistersAt`. -/
abbrev LiveDispatchCoordinates (p : Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalStep.Payload rate ×
    (LiveDiscrete p × (Fin p.T × CompletePublicTable.CompleteRow p))

/-- Decode the accepted lossless live registers, then perform precisely the
canonical step's time reindexing on registers and owned queues. -/
def liveInputOfCoordinates (z : LiveDispatchCoordinates p rate) :
    CoordinatorRoundDispatch.LiveInput p :=
  let r := decodeLiveRegisters z.1 z.2.1
  let q := decodeLiveOwned z.1 z.2.1
  { eta := rate.eta
    registers := ReferenceActivePhysicalStep.liveRegistersAt r z.2.2.1
    ownedRegisters := ReferenceActivePhysicalStep.liveOwnedAt r q z.2.2.1
    followerBaseScore := z.2.1.baseScores
    row := z.2.2.2 }

/-- The original LIVE arguments and canonical full round, in the coordinates
consumed by `liveInputOfCoordinates`. -/
def liveDispatchCoordinatesOfRound
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) : LiveDispatchCoordinates p rate :=
  (r.payload, (encodeLive r q base, (x.time, x.row)))

/-- Decoding the stored complement scores recovers every actual score. -/
theorem decodeLiveRegisters_encodeLive
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) :
    decodeLiveRegisters r.payload (encodeLive r q base) = r := by
  have h := decodeCoordinator_encodeCoordinator
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base)
  change ReferenceActivePhysicalStep.CoordinatorConfiguration.live
      (decodeLiveRegisters r.payload (encodeLive r q base))
      (decodeLiveOwned r.payload (encodeLive r q base)) base =
    ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base at h
  injection h with hr hq hb

/-- Decoding the stored owned queues recovers the exact dependent owned
register, including its previous-service vector. -/
theorem decodeLiveOwned_encodeLive
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) :
    HEq (decodeLiveOwned r.payload (encodeLive r q base)) q := by
  have h := decodeCoordinator_encodeCoordinator
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base)
  change ReferenceActivePhysicalStep.CoordinatorConfiguration.live
      (decodeLiveRegisters r.payload (encodeLive r q base))
      (decodeLiveOwned r.payload (encodeLive r q base)) base =
    ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base at h
  injection h with hr hq hb

/-- Apply a live coordinator configuration to the actual round coordinate.
The `Option` keeps this eliminator total on the canonical phase sum. -/
def liveInputOptionOfCoordinator (roundTime : Fin p.T)
    (row : CompletePublicTable.CompleteRow p) :
    ReferenceActivePhysicalStep.CoordinatorConfiguration p rate →
      Option (CoordinatorRoundDispatch.LiveInput p)
  | .live r q base => some {
      eta := rate.eta
      registers := ReferenceActivePhysicalStep.liveRegistersAt r roundTime
      ownedRegisters := ReferenceActivePhysicalStep.liveOwnedAt r q roundTime
      followerBaseScore := base
      row := row }
  | _ => none

/-- The decoded and reindexed local input is definitionally the exact one-call
input used by the original canonical live branch. -/
theorem liveInputOfCoordinates_liveDispatchCoordinatesOfRound
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) :
    liveInputOfCoordinates (liveDispatchCoordinatesOfRound x r q base) =
      ReferenceActivePhysicalStep.liveInput x r q base := by
  have h := decodeCoordinator_encodeCoordinator
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base)
  change ReferenceActivePhysicalStep.CoordinatorConfiguration.live
      (decodeLiveRegisters r.payload (encodeLive r q base))
      (decodeLiveOwned r.payload (encodeLive r q base)) base =
    ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base at h
  have hinput := congrArg (liveInputOptionOfCoordinator (p := p) (rate := rate)
    x.time x.row) h
  change some (liveInputOfCoordinates (liveDispatchCoordinatesOfRound x r q base)) =
    some (ReferenceActivePhysicalStep.liveInput x r q base) at hinput
  exact Option.some.inj hinput

/-- On an original canonical round whose coordinator is live, the canonical
dispatcher uses this exact local `dispatchLive` call. -/
theorem canonicalDispatch_live_reconstruction
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator =
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base) :
    ReferenceActivePhysicalStep.dispatch x =
      ReferenceActivePhysicalStep.DispatchCut.live r q base
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x r q base)) := by
  rw [ReferenceActivePhysicalStep.dispatch, hstate]
  change (match CoordinatorRoundDispatch.dispatch
      (.live (ReferenceActivePhysicalStep.liveInput x r q base)) with
    | .live outcome => ReferenceActivePhysicalStep.DispatchCut.live r q base outcome) = _
  rw [CoordinatorRoundDispatch.dispatch]
  rfl

/-- Equality of local inputs transports the actual dependent dispatcher result
without changing any runtime field. -/
theorem dispatchLive_congr {x y : CoordinatorRoundDispatch.LiveInput p}
    (h : x = y) :
    h ▸ CoordinatorRoundDispatch.dispatchLive x =
      CoordinatorRoundDispatch.dispatchLive y := by
  cases h
  rfl

/-- The coordinate-dispatched outcome transports without changing any field
to the exact original canonical live input. This is the dependent pointwise
reconstruction consumed by `canonicalDispatch_live_reconstruction`. -/
theorem dispatchLive_coordinates_reconstruction
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) :
    (liveInputOfCoordinates_liveDispatchCoordinatesOfRound x r q base) ▸
        CoordinatorRoundDispatch.dispatchLive
          (liveInputOfCoordinates (liveDispatchCoordinatesOfRound x r q base)) =
      CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x r q base) := by
  exact dispatchLive_congr
    (liveInputOfCoordinates_liveDispatchCoordinatesOfRound x r q base)

/-- The down-facing view reconstructed by the local dispatch observation is
exactly the canonical dispatch cut's view. -/
theorem canonicalDispatch_live_downView
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator =
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base) :
    (ReferenceActivePhysicalStep.dispatch x).downView =
      (ReferenceActivePhysicalStep.DispatchCut.live r q base
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x r q base))).downView := by
  rw [canonicalDispatch_live_reconstruction x r q base hstate]

/-- The selected arm or the source fallback is preserved by the same exact
canonical dispatch reconstruction. -/
theorem canonicalDispatch_live_arm
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator =
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base) :
    (ReferenceActivePhysicalStep.dispatch x).arm =
      (ReferenceActivePhysicalStep.DispatchCut.live r q base
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x r q base))).arm := by
  rw [canonicalDispatch_live_reconstruction x r q base hstate]

end Bandits.Support.ReferenceLiveDispatchMeasurability

end
