/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstDownAwaitedAmbiguity
public import Bandits.Support.ReferenceActiveHorizonMeasurability

/-!
# Actual completed DOWN ambiguity as a Borel event

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-55,74-124`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-46`.

The observations below project the existing physical run on its whole active
input carrier. Real rows and saved buffers retain their original measurable
spaces. The countable projections retain actual optional calls, grid feedback,
initial registers and logged decoder diagnostics, including failures.

This is an internal target for the conditional second-awaited-completion
branch. It is not the source ambiguity event: generated launch and awaited-word
provenance, stopping including the first overflow update, the adaptive original
source law, global coverage and probability estimates remain separate work.

The Borel results take only `{p}`, `{rate}`, `start`, `count`,
`span : start + count ≤ p.T` and `i : Fin (p.m - 1)`. Their domain is exactly
`ActiveRunInput start`: the original state, WHOLE complete rows, original J,
and WHOLE grid rewards, restricted only by all-active-at-start typing.
The launched consumer preserves all 31 outer inputs of its admitted producer;
its count equality stays inside the result after the actual seed witness.
No unconditional launch, count attainment, service/delivery, first-overflow
identity, probability bound or main-regret conclusion is claimed.

Only direct project dependencies: `ReferenceFirstDownAwaitedAmbiguity`
`35b0c8b897427e9608a39ca5f35a6b8d3d30332ff2d0d684e66ed5c6a6e0a54f`
and `ReferenceActiveHorizonMeasurability`
`a2eeb8ffa0160d8807ab1fab7c5758776dabb0c4a14fdc594c996572a849fdc0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

local instance : MeasurableSingletonClass
    (ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate) := ⟨fun _ => trivial⟩

private theorem measurableSet_option_singleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] {a} := by
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e := comap_measurable _
  have hset : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := α)

local instance {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] :
    @MeasurableSingletonClass (Option α) LaterAssignmentStartMeasurability.optionMeasurableSpace :=
  ⟨measurableSet_option_singleton⟩

/-- A literal stamped call, with its full sample and original grid index. -/
abbrev DownCallCode (p : Parameters) :=
  Fin p.T × (Bool × (Bool × (AffineChannelLaw.Sample (AffineBatchDecoder.width p) × Fin (D p + 1))))

/-- Decode the grid reward by the original denominator, without rounding again. -/
def decodeCall (code : DownCallCode p) : ReferenceFollowerDownDecoderReplay.Call p :=
  (code.1, ⟨code.2.1, code.2.2.1, code.2.2.2.1,
    (ActualInitializationPhysicalStep.observationOfGrid p code.2.2.2.2).val.val⟩)

/-- Only discrete registers are projected; the continuous carried buffer is
neither replaced nor given a discrete measurable structure. -/
def incomingRegisters (incoming : FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :
    Option (FollowerDownMeasurability.FollowerStateCode p rate) :=
  incoming.map fun data => data.1.1.1

private theorem measurable_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ) (hf : ∀ a, Measurable (fun b : β a => f ⟨a, b⟩)) :
    Measurable f := by
  intro s hs
  change MeasurableSet[(⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    (f ⁻¹' s)
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

private theorem measurable_carryRegisters :
    Measurable (fun carry : FollowerObservationStageMeasurabilityRepair.CarriedState p rate =>
      carry.1.1) := by
  apply measurable_sigma_sections
  intro index
  change Measurable (fun _ : FollowerDownMeasurability.SavedScalarFamily index.2.1 => index.1)
  exact measurable_const

theorem measurable_incomingRegisters :
    Measurable (incomingRegisters (p := p) (rate := rate)) := by
  have h : Measurable (fun value : Unit ⊕
      (FollowerObservationStageMeasurabilityRepair.CarriedState p rate ×
        FollowerPrepareJointMeasurability.LocalMemoryCode p) =>
      Sum.elim (fun _ => none) (fun data => some data.1.1.1) value) :=
    Measurable.sumElim measurable_const
      ((measurable_of_countable (fun code : FollowerDownMeasurability.FollowerStateCode p rate =>
        some code)).comp (measurable_carryRegisters.comp measurable_fst))
  convert h.comp (FollowerPrepareJointMeasurability.measurable_incomingConfigurationToSum rate) using 1
  funext incoming
  cases incoming <;> rfl

theorem incomingRegisters_actual (config : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    incomingRegisters (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate config) =
      match config with
      | .dagger => none
      | .ordinary state _ => some (FollowerDownMeasurability.followerStateCode rate state) := by
  cases config <;> rfl

/-- The actual prepared ordinary registers, or honest dagger absence. -/
def preparedRegisters (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1)) :=
  incomingRegisters (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode x i).2.2.2

theorem measurable_preparedRegisters (i : Fin (p.m - 1)) :
    Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate => preparedRegisters x i) := by
  have h : Measurable (fun code : FollowerVaryingActivationMeasurability.VaryingPreparedOutput p rate =>
      incomingRegisters code.2.2.2) := by
    apply measurable_sigma_sections
    intro activation
    exact measurable_incomingRegisters.comp (measurable_snd.comp measurable_snd)
  exact h.comp (ReferenceActivePhysicalStepMeasurability.measurable_preparedFollowerCode i)

private theorem registers_reconstruct
    (carry : FollowerObservationStageMeasurabilityRepair.CarriedState p rate) :
    FollowerDownMeasurability.followerStateCode rate
      (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState carry.1 carry.2) = carry.1.1 := by
  have hstatus (status : Fin 3) : FollowerDownMeasurability.followerStatusCode
      (FollowerDownMeasurability.followerStatusOfCode status) = status := by
    fin_cases status <;> rfl
  rcases carry with ⟨⟨code, skeleton⟩, values⟩
  cases code
  simp only [FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
    FollowerDownMeasurability.followerStateOfCode, FollowerDownMeasurability.followerStateCode,
    hstatus, FollowerDownMeasurability.decoderBatchOfCode,
    FollowerDownMeasurability.decoderBatchCode, List.map_map, Function.comp_def,
    FollowerDownMeasurability.decoderEntryCode, FollowerDownMeasurability.decoderEntryOfCode,
    Prod.eta, List.map_id']

private theorem preparedRegisters_actual
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1)) :
    preparedRegisters record.input i =
      match ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i with
      | .dagger => none
      | .ordinary state _ => some (FollowerDownMeasurability.followerStateCode rate state) := by
  have h := congrArg (fun round : DeclaredFollowerLocalRound.PreparedRound p rate =>
    round.configuration)
    (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode_reconstruct record.input i)
  have hout := congrArg (fun output : ReferenceActivePhysicalStep.RoundOutput record.input =>
    (output.preparation.followers.followers i).configuration) record.output_eq
  have heq : FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
      (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode record.input i).2.2.2 =
      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i := h.trans hout.symm
  unfold preparedRegisters
  rw [← heq]
  cases (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode record.input i).2.2.2 with
  | none => rfl
  | some data =>
      exact congrArg some (registers_reconstruct data.1).symm

/-- Full own feedback, from the retained whole-step code. -/
def ownGrid (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1)) : Fin (D p + 1) :=
  (ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1.2.2.2.1
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)

private theorem measurable_ownGrid (i : Fin (p.m - 1)) :
    Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate => ownGrid x i) :=
  (measurable_pi_apply _).comp (measurable_fst.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp
      (measurable_fst.comp ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode)))))

/-- Countable code for the actual prepared call; unselected and disabled calls
remain present. The sample is always the focal follower's own DOWN coordinate. -/
def roundCallObservation (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1)) :
    Option (DownCallCode p) := by
  classical
  exact (preparedRegisters x i).map fun registers =>
    (x.time, decide (ActiveFollowerDownAcceptance.downSelected p i x.row x.time),
      decide (FollowerDownMeasurability.followerStatusOfCode registers.status = .unoccupied),
      (x.row.2 x.time).2 (0, i), ownGrid x i)

theorem measurable_roundCallObservation (i : Fin (p.m - 1)) :
    Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate => roundCallObservation x i) := by
  classical
  have hselection : Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
      decide (ActiveFollowerDownAcceptance.downSelected p i x.row x.time)) := by
    have h : Measurable (fun z : CompletePublicTable.CompleteRow p × Fin p.T =>
        decide (ActiveFollowerDownAcceptance.downSelected p i z.1 z.2)) := by
      apply measurable_from_prod_countable_left
      intro time
      exact FollowerDownJointMeasurability.measurable_downSelectedAt p i time
    exact h.comp (ReferenceActivePhysicalStepMeasurability.measurable_row.prodMk
      ReferenceActivePhysicalStepMeasurability.measurable_time)
  have hsample : Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
      (x.row.2 x.time).2 (0, i)) := by
    have h : Measurable (fun z : CompletePublicTable.CompleteRow p × Fin p.T =>
        (z.1.2 z.2).2 (0, i)) := by
      apply measurable_from_prod_countable_left
      intro time
      exact (measurable_pi_apply (0, i)).comp (measurable_snd.comp
        ((measurable_pi_apply time).comp measurable_snd))
    exact h.comp (ReferenceActivePhysicalStepMeasurability.measurable_row.prodMk
      ReferenceActivePhysicalStepMeasurability.measurable_time)
  exact (measurable_of_countable (fun z : Option (FollowerDownMeasurability.FollowerStateCode p rate) ×
      (Fin p.T × (Bool × (AffineChannelLaw.Sample (AffineBatchDecoder.width p) × Fin (D p + 1)))) =>
        z.1.map fun registers => (z.2.1, z.2.2.1,
          decide (FollowerDownMeasurability.followerStatusOfCode registers.status = .unoccupied),
          z.2.2.2.1, z.2.2.2.2))).comp
    ((measurable_preparedRegisters i).prodMk (ReferenceActivePhysicalStepMeasurability.measurable_time.prodMk
      (hselection.prodMk (hsample.prodMk (measurable_ownGrid i)))))

/-- The code is formed on the original retained input, without a second run. -/
def downCallObservation (i : Fin (p.m - 1)) (record : ReferenceFollowerDownDecoderReplay.Record p rate) :=
  roundCallObservation record.input i

private theorem record_row (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1)) :
    ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i = record.input.row :=
  (record.output.preparation.follower_alignment i).1

private theorem record_grid (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1)) :
    ownGrid record.input i = record.gridFeedback
      (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
  exact congrFun (ReferenceActiveHorizonMeasurability.roundRecordCode_front record).2.2.2 _

private theorem record_observation
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) (i : Fin (p.m - 1)) :
    ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i =
      ActualInitializationPhysicalStep.observationOfGrid p (ownGrid record.input i) := by
  rw [record_grid]
  exact record.output.preparation.feedback.observations_eq _

/-- Lossless identity with the very same actual optional runtime call. -/
theorem downCallObservation_reconstructs (i : Fin (p.m - 1)) (record : ReferenceFollowerDownDecoderReplay.Record p rate) :
    (downCallObservation i record).map decodeCall =
      ReferenceFollowerDownDecoderReplay.actualDownCall i record := by
  classical
  unfold downCallObservation roundCallObservation
  rw [preparedRegisters_actual]
  cases hconfig : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i with
  | dagger => simp only [Option.map_none, ReferenceFollowerDownDecoderReplay.actualDownCall, hconfig]
  | ordinary state memory =>
      simp only [Option.map_some, ReferenceFollowerDownDecoderReplay.actualDownCall, hconfig]
      rw [record_row, ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime, record_observation]
      simp only [decodeCall, ActiveFollowerDownAcceptance.currentRoundInput,
        ActiveFollowerDownAcceptance.downSelected, FollowerDownMeasurability.followerStateCode,
        FollowerDownMeasurability.followerStatusOfCode_code]
      congr 3
      exact decide_eq_decide.mpr Iff.rfl

/-- Dagger is the only absent prepared call. Ineligible administrative calls
remain in the observation with their actual fields. -/
theorem downCallObservation_eq_none_iff (i : Fin (p.m - 1))
    (record : ReferenceFollowerDownDecoderReplay.Record p rate) :
    downCallObservation i record = none ↔
      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i = .dagger := by
  unfold downCallObservation roundCallObservation
  rw [preparedRegisters_actual]
  cases ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i <;>
    simp only [Option.map_none, Option.map_some, reduceCtorEq]

/-- Raw output, expected word, comparison and ordinary acceptance are retained
as separate discrete fields of the actual cut. -/
abbrev DownCutFields (p : Parameters) :=
  Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) ×
    (Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) × (Option Bool × Bool))

/-- The event uses raw output, expected word, comparison and ordinary acceptance
as distinct fields. Full failure reasons remain in the diagnostic projection. -/
def cutFields (cut : ReferenceDownReception.ReferenceDownCutOutput p rate) : DownCutFields p := by
  classical
  exact (cut.raw, cut.expectedWord, cut.rawComparison, decide cut.ordinaryAcceptance)

def cutCodeFields (cut : ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate) :
    DownCutFields p := (cut.raw, cut.expectedWord, cut.rawComparison, cut.ordinaryAcceptance)

/-- The logged registers include the entire pending/completed bank. The
projection retains absence, full failure reasons and the needed cut fields. -/
abbrev DownDiagnosticCode (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Option (FollowerDownMeasurability.FollowerStateCode p rate) ×
    (Option DeclaredFollowerLocalRound.RoundFailure × Option (DownCutFields p))

def diagnosticProjection (output : ReferenceFollowerTailComposition.FollowerObservable p rate) :
    DownDiagnosticCode p rate :=
  (match output.2.2.1 with | .inl _ => none | .inr carry => some carry.1.1,
    output.2.1,
    match output.2.2.1 with
    | .inl _ => none
    | .inr _ => output.2.2.2.map cutCodeFields)

private theorem measurable_diagnosticProjection :
    Measurable (diagnosticProjection (p := p) (rate := rate)) := by
  have hlogged : Measurable (fun input : ReferenceFollowerTailComposition.DownInputObservable p rate =>
      match input with | .inl _ => none | .inr carry => some carry.1.1) :=
    Measurable.sumElim measurable_const
      ((measurable_of_countable (fun code : FollowerDownMeasurability.FollowerStateCode p rate =>
        some code)).comp
        measurable_carryRegisters)
  have htag : Measurable (fun input : ReferenceFollowerTailComposition.DownInputObservable p rate =>
      input.isRight) := Measurable.sumElim measurable_const measurable_const
  have hinput : Measurable (fun output : ReferenceFollowerTailComposition.FollowerObservable p rate =>
      output.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hcut : Measurable (fun output : ReferenceFollowerTailComposition.FollowerObservable p rate =>
      match output.2.2.1 with
      | .inl _ => none
      | .inr _ => output.2.2.2.map cutCodeFields) := by
    have h := (measurable_of_countable (fun z : Bool ×
        Option (ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate) =>
          if z.1 then z.2.map cutCodeFields else none)).comp
      ((htag.comp hinput).prodMk (measurable_snd.comp
        (measurable_snd.comp measurable_snd)))
    convert h using 1
    funext output
    dsimp only [Function.comp_def]
    rcases output with ⟨incoming, failure, input, cut⟩
    cases input <;> rfl
  exact (hlogged.comp hinput).prodMk ((measurable_fst.comp measurable_snd).prodMk hcut)

private theorem diagnosticProjection_reconstruct
    (output : ReferenceFollowerTailComposition.FollowerObservable p rate) :
    diagnosticProjection output =
      ((ReferenceFollowerTailComposition.reconstructFollowerObservable output).downInput.map
        (FollowerDownMeasurability.followerStateCode rate),
       (ReferenceFollowerTailComposition.reconstructFollowerObservable output).failure,
       (ReferenceFollowerTailComposition.reconstructFollowerObservable output).down.map cutFields) := by
  rcases output with ⟨incoming, failure, input, cut⟩
  cases input with
  | inl absent => rfl
  | inr carry =>
      cases cut with
      | none =>
          simp only [diagnosticProjection, ReferenceFollowerTailComposition.reconstructFollowerObservable,
            ReferenceFollowerTailComposition.reconstructDownInput,
            ReferenceFollowerTailComposition.reconstructDown, Option.map_some,
            Option.map_none, ReferenceFollowerTailComposition.reconstructCarry, registers_reconstruct]
      | some code =>
          simp only [diagnosticProjection, ReferenceFollowerTailComposition.reconstructFollowerObservable,
            ReferenceFollowerTailComposition.reconstructDownInput,
            ReferenceFollowerTailComposition.reconstructDown, Option.map_some,
            ReferenceFollowerTailComposition.reconstructCarry, registers_reconstruct]
          congr 2
          simp only [cutCodeFields, cutFields,
            ReferenceDownReceptionMeasurability.reconstructReferenceDownCutCode,
            decide_eq_true_eq]
          cases code.ordinaryAcceptance <;> rfl

abbrev DownRoundCode (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Fin p.T × (Fin (D p + 1) × (Option (DownCallCode p) × DownDiagnosticCode p rate))

def roundDownObservation (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1)) :
    DownRoundCode p rate :=
  (x.time, ownGrid x i, roundCallObservation x i,
    diagnosticProjection ((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).2.1 i))

theorem measurable_roundDownObservation (i : Fin (p.m - 1)) :
    Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate => roundDownObservation x i) :=
  ReferenceActivePhysicalStepMeasurability.measurable_time.prodMk ((measurable_ownGrid i).prodMk
    ((measurable_roundCallObservation i).prodMk
      (measurable_diagnosticProjection.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_snd.comp
          ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode))))))

private theorem record_diagnostics (record : ReferenceFollowerDownDecoderReplay.Record p rate)
    (i : Fin (p.m - 1)) :
    (roundDownObservation record.input i).2.2.2 =
      ((record.output.followers i).downInput.map (FollowerDownMeasurability.followerStateCode rate),
        (record.output.followers i).failure, (record.output.followers i).down.map cutFields) := by
  rw [show (roundDownObservation record.input i).2.2.2 =
      diagnosticProjection ((ReferenceActiveStepCompositionMeasurability.wholeStepCode record.input).2.1 i)
      from rfl, diagnosticProjection_reconstruct]
  have hd := (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs record).2.2.1 i
  change ReferenceFollowerTailComposition.reconstructFollowerObservable
      ((ReferenceActiveStepCompositionMeasurability.wholeStepCode record.input).2.1 i) =
        record.output.followers i at hd
  rw [hd]

/-- The existing computed prefix provides the next canonical input. -/
def prefixInput (start k : ℕ) (span : start + (k + 1) ≤ p.T)
    (x : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start) :
    ReferenceActivePhysicalStep.RoundInput p rate :=
  ReferenceActivePhysicalHorizon.roundInputAt x.val.1 x.val.2.1 x.val.2.2.1 x.val.2.2.2
    start x.property (ReferenceActiveHorizonMeasurability.runOfInput start k (by omega) x)
    ⟨start + k, by omega, by omega⟩

theorem measurable_prefixInput (start k : ℕ) (span : start + (k + 1) ≤ p.T) :
    Measurable (prefixInput (p := p) (rate := rate) start k span) := by
  have hdata : Measurable (fun x : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) start => x.val) :=
    measurable_subtype_coe
  have hcoordinates : Measurable (fun x : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) start =>
      ((ReferenceActiveHorizonMeasurability.runOfInput start k (by omega) x).finalState,
        x.val.2.1, x.val.2.2.1, (⟨start + k, by omega⟩ : Fin p.T), x.val.2.2.2)) :=
    (ReferenceActiveHorizonMeasurability.measurable_runFinalState start k (by omega)).prodMk
    ((measurable_fst.comp (measurable_snd.comp hdata)).prodMk
      ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hdata))).prodMk
        (measurable_const.prodMk
          (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hdata))))))
  apply measurable_comap_iff.mpr
  exact hcoordinates.subtype_mk

/-- Each chronological record is the step on its own computed prefix. -/
theorem run_records_eq_ofFn (start count : ℕ) (span : start + count ≤ p.T)
    (x : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start) :
    (ReferenceActiveHorizonMeasurability.runOfInput start count span x).records =
      List.ofFn (fun k : Fin count =>
      (⟨prefixInput start k.val (by omega) x,
        ReferenceActivePhysicalStep.step (prefixInput start k.val (by omega) x), rfl⟩ :
        ReferenceFollowerDownDecoderReplay.Record p rate)) := by
  induction count with
  | zero =>
      exact ReferenceActivePhysicalHorizon.run_zero_records _ _ _ _ _ _ _
  | succ count ih =>
      rw [ReferenceActiveHorizonMeasurability.runOfInput, ReferenceActivePhysicalHorizon.run_successor_step]
      rw [(ReferenceActivePhysicalHorizon.foldRound_equations _ _ _ _ _ _ _ _).2]
      rw [List.ofFn_succ', List.concat_eq_append]
      change (ReferenceActiveHorizonMeasurability.runOfInput start count (by omega) x).records ++ [_] = _
      rw [ih (by omega)]
      rfl

/-- The initial code and one countable observation per original calendar round.
The finite array is merely an index for the chronological retained list. -/
abbrev RunDownObservationCode (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) (count : ℕ) :=
  Option (FollowerDownMeasurability.FollowerStateCode p rate) × (Fin count → DownRoundCode p rate)

def runDownObservation (start count : ℕ) (span : start + count ≤ p.T)
    (i : Fin (p.m - 1))
    (x : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start) :
    RunDownObservationCode p rate count :=
  (incomingRegisters (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
      (x.val.1.followers i)),
    fun k => roundDownObservation (prefixInput start k.val (by omega) x) i)

/-- Exact initial configuration projection and exact chronological records. -/
theorem runDownObservation_eq_actual (start count : ℕ) (span : start + count ≤ p.T)
    (i : Fin (p.m - 1))
    (x : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start) :
    (runDownObservation start count span i x).1 =
      (match x.val.1.followers i with
      | .dagger => none
      | .ordinary state _ => some (FollowerDownMeasurability.followerStateCode rate state)) ∧
    List.ofFn (runDownObservation start count span i x).2 =
      (ReferenceActiveHorizonMeasurability.runOfInput start count span x).records.map (fun record =>
        roundDownObservation record.input i) := by
  constructor
  · exact incomingRegisters_actual _
  · rw [run_records_eq_ofFn, List.map_ofFn]
    rfl

/-- The decoded initial bank is the literal initial bank or honest absence,
including at zero horizon; no empty-bank default is introduced. -/
theorem runDownObservation_initialBank_eq_actual (start count : ℕ)
    (span : start + count ≤ p.T) (i : Fin (p.m - 1))
    (x : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start) :
    (runDownObservation start count span i x).1.map
      (fun code => FollowerDownMeasurability.decoderBatchOfCode code.downBatch) =
      match x.val.1.followers i with
      | .dagger => none
      | .ordinary state _ => some state.downBatch := by
  rw [(runDownObservation_eq_actual start count span i x).1]
  cases x.val.1.followers i with
  | dagger => rfl
  | ordinary state memory =>
      exact congrArg some (FollowerDownMeasurability.decoderBatchOfCode_code state.downBatch)

theorem measurable_runDownObservation (start count : ℕ) (span : start + count ≤ p.T)
    (i : Fin (p.m - 1)) :
    Measurable (runDownObservation (p := p) (rate := rate) start count span i) := by
  have hinitial : Measurable (fun x : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) start =>
      incomingRegisters (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
        (x.val.1.followers i))) :=
    measurable_incomingRegisters.comp
    ((measurable_pi_apply i).comp (ReferenceActivePhysicalStepMeasurability.measurable_followerCodes.comp
      (measurable_fst.comp measurable_subtype_coe)))
  exact hinitial.prodMk (measurable_pi_iff.mpr fun k =>
    (measurable_roundDownObservation i).comp (measurable_prefixInput start k.val (by omega)))

/-- Decoded calls in their original chronological order. -/
def observedCalls {count : ℕ} (code : RunDownObservationCode p rate count) :
    List (ReferenceFollowerDownDecoderReplay.Call p) :=
  (List.ofFn code.2).filterMap fun record => record.2.2.1.map decodeCall

/-- Every positive keeps its original timestamp and sample. -/
theorem observedCalls_eq_actual (start count : ℕ) (span : start + count ≤ p.T)
    (i : Fin (p.m - 1))
    (x : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start) :
    observedCalls (runDownObservation start count span i x) =
      ReferenceFollowerDownDecoderReplay.actualDownCalls i
        (ReferenceActiveHorizonMeasurability.runOfInput start count span x).records := by
  unfold observedCalls
  rw [(runDownObservation_eq_actual start count span i x).2, List.filterMap_map]
  apply List.filterMap_congr
  intro record _
  exact downCallObservation_reconstructs i record

theorem observedPositives_eq_actual (start count : ℕ) (span : start + count ≤ p.T)
    (i : Fin (p.m - 1))
    (x : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start) :
    ReferenceFollowerDownDecoderReplay.positiveCallEntries
        (observedCalls (runDownObservation start count span i x)) =
      ReferenceFollowerDownDecoderReplay.actualDownPositives i
        (ReferenceActiveHorizonMeasurability.runOfInput start count span x).records := by
  rw [observedCalls_eq_actual]
  rfl

/-- Fixed indexed calls on the whole original run-input carrier are Borel. -/
theorem measurable_indexedDownCall (start count : ℕ) (span : start + count ≤ p.T)
    (i : Fin (p.m - 1)) (k : Fin count) :
    Measurable (fun x : ReferenceActiveHorizonMeasurability.ActiveRunInput
        (p := p) (rate := rate) start =>
      (runDownObservation start count span i x).2 k |>.2.2.1) :=
  (measurable_roundCallObservation i).comp (measurable_prefixInput start k.val (by omega))

/-- Diagnostics are projected only after the original mixed list is measured.
Its indexed sum tags retain honest absence outside the chronological list. -/
theorem measurable_retainedDiagnosticAt (start count : ℕ) (span : start + count ≤ p.T)
    (i : Fin (p.m - 1)) (n : ℕ) :
    Measurable (fun x : ReferenceActiveHorizonMeasurability.ActiveRunInput
        (p := p) (rate := rate) start =>
      ReferenceActiveHorizonMeasurability.listObservationAt
        ((ReferenceActiveHorizonMeasurability.runObservation start count span x).2.map
          (fun code => diagnosticProjection (code.2.2.2.1 i))) n) := by
  have hproject : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) => diagnosticProjection (code.2.2.2.1 i)) :=
    measurable_diagnosticProjection.comp ((measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  have hlist := ReferenceActiveHorizonMeasurability.measurable_list_map
    (fun x : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start =>
      (ReferenceActiveHorizonMeasurability.runObservation start count span x).2)
    (measurable_snd.comp (ReferenceActiveHorizonMeasurability.measurable_runObservation start count span))
    _ hproject
  exact (measurable_pi_apply n).comp (measurable_snd.comp
    (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hlist))

open ReferenceFollowerDownDecoderReplay AffineBatchDecoder
open ReferenceActiveHorizonMeasurability FollowerDownMeasurability

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The first component of the existing decoder on the logged discrete bank.
Only its enable bit changes from the prepared call to the logged status. -/
def decodedLoggedBank (call : DownCallCode p) (logged : FollowerStateCode p rate) :
    AffineBatchDecoder.State p.T (width p) := by
  classical
  exact (decodeStep p (ActiveFollowerDownAcceptance.currentInputExtension p
    { (decodeCall call).2 with
      receiverEnabled := decide (followerStatusOfCode logged.status = .unoccupied) })
    (decoderBatchOfCode logged.downBatch) call.1).1

private theorem decodedLoggedBank_actual (i : Fin (p.m - 1)) (record : Record p rate)
    (call : DownCallCode p) (hcall : downCallObservation i record = some call)
    (logged : ReferencePrelaunchFollower.State p rate.eta) :
    decodedLoggedBank call (followerStateCode rate logged) =
      (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
        (preparedOwnObservation record i) rate logged).1 := by
  classical
  unfold downCallObservation roundCallObservation at hcall
  obtain ⟨registers, _, heq⟩ := Option.map_eq_some_iff.mp hcall
  subst call
  rw [record_observation]
  simp only [decodedLoggedBank, decodeCall, followerStateCode,
    followerStatusOfCode_code, decoderBatchOfCode_code,
    ActiveFollowerDownAcceptance.currentDecodeStep,
    ActiveFollowerDownAcceptance.currentRoundInput,
    ActiveFollowerDownAcceptance.downSelected]
  congr 4
  exact decide_eq_decide.mpr Iff.rfl

/-- The finite observation's literal second-completion cylinder. All tests
are on the already produced countable code; no premise package is supplied. -/
private def completionCodeSet
    (seed : AffineBatchDecoder.State p.T (width p))
    (positives window : List (Entry p.T (width p))) : Set (DownRoundCode p rate) :=
  {round | ∃ (entry : Entry p.T (width p)) (call : DownCallCode p)
      (logged : FollowerStateCode p rate) (cut : DownCutFields p)
      (word : AffineChannelLaw.Word (width p)),
    entry ∈ window ∧ entry.time = round.1 ∧ round.2.2.1 = some call ∧
    call.1 = round.1 ∧ entry.time = call.1 ∧ entry.sample = (decodeCall call).2.sample ∧
    0 < (ActualInitializationPhysicalStep.observationOfGrid p round.2.1).val.val ∧
    round.2.2.2.1 = some logged ∧ round.2.2.2.2.2 = some cut ∧
    cut.2.2.1.isSome = true ∧ cut.2.2.1 = some false ∧
    cut.1 = batchOutput window ∧ cut.1 = none ∧ cut.2.1 = some word ∧
    decodedLoggedBank call logged =
      ⟨[], seed.completed ++
        [seed.pending ++ positives.take (quota p - seed.pending.length), window]⟩ ∧
    satisfies (samples window) word ∧ ∃ other, other ≠ word ∧ satisfies (samples window) other}

/-- Actual runtime formula on the whole input carrier. Its seed is the literal
initial ordinary bank, and its witness is a real retained completion record. -/
def secondDownAmbiguityEvent (start count : ℕ) (span : start + count ≤ p.T)
    (i : Fin (p.m - 1)) : Set (ActiveRunInput (p := p) (rate := rate) start) :=
  {x | ∃ (seed : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
    x.val.1.followers i = .ordinary seed memory ∧
    let positives := actualDownPositives i (runOfInput start count span x).records
    let needed := quota p - seed.downBatch.pending.length
    let window := positives.drop needed
    seed.downBatch.pending.length < quota p ∧ positives.length = needed + quota p ∧
    window.length = quota p ∧
    ∃ (entry : Entry p.T (width p)) (record : Record p rate) (call : Call p)
      (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (word : AffineChannelLaw.Word (width p)),
      entry ∈ window ∧ entry.time = record.input.time ∧
      record ∈ (runOfInput start count span x).records ∧ actualDownCall i record = some call ∧
      call.1 = record.input.time ∧ entry.time = call.1 ∧ entry.sample = call.2.sample ∧
      0 < (preparedOwnObservation record i).val.val ∧
      (record.output.followers i).downInput = some logged ∧
      (record.output.followers i).down = some cut ∧
      cut.rawComparison.isSome = true ∧ cut.rawComparison = some false ∧
      cut.raw = batchOutput window ∧ cut.raw = none ∧ cut.expectedWord = some word ∧
      (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
        (preparedOwnObservation record i) rate logged).1 =
        ⟨[], seed.downBatch.completed ++ [seed.downBatch.pending ++ positives.take needed, window]⟩ ∧
      satisfies (samples window) word ∧ ∃ other, other ≠ word ∧ satisfies (samples window) other}

/-- The event's complete physical characterization, including the mixed first
batch and the consistent word distinguishing ambiguity from inconsistency. -/
theorem mem_secondDownAmbiguityEvent_iff (start count : ℕ) (span : start + count ≤ p.T)
    (i : Fin (p.m - 1)) (x : ActiveRunInput (p := p) (rate := rate) start) :
    x ∈ secondDownAmbiguityEvent start count span i ↔
    ∃ (seed : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
    x.val.1.followers i = .ordinary seed memory ∧
    let positives := actualDownPositives i (runOfInput start count span x).records
    let needed := quota p - seed.downBatch.pending.length
    let window := positives.drop needed
    seed.downBatch.pending.length < quota p ∧ positives.length = needed + quota p ∧
    window.length = quota p ∧
    ∃ (entry : Entry p.T (width p)) (record : Record p rate) (call : Call p)
      (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (word : AffineChannelLaw.Word (width p)),
      entry ∈ window ∧ entry.time = record.input.time ∧
      record ∈ (runOfInput start count span x).records ∧ actualDownCall i record = some call ∧
      call.1 = record.input.time ∧ entry.time = call.1 ∧ entry.sample = call.2.sample ∧
      0 < (preparedOwnObservation record i).val.val ∧
      (record.output.followers i).downInput = some logged ∧
      (record.output.followers i).down = some cut ∧
      cut.rawComparison.isSome = true ∧ cut.rawComparison = some false ∧
      cut.raw = batchOutput window ∧ cut.raw = none ∧ cut.expectedWord = some word ∧
      (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
        (preparedOwnObservation record i) rate logged).1 =
        ⟨[], seed.downBatch.completed ++ [seed.downBatch.pending ++ positives.take needed, window]⟩ ∧
      satisfies (samples window) word ∧ ∃ other, other ≠ word ∧ satisfies (samples window) other := Iff.rfl

private theorem completionCodeSet_iff
    (seed : AffineBatchDecoder.State p.T (width p))
    (positives window : List (Entry p.T (width p))) (record : Record p rate)
    (i : Fin (p.m - 1)) :
    roundDownObservation record.input i ∈ completionCodeSet seed positives window ↔
    ∃ (entry : Entry p.T (width p)) (call : Call p)
      (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (word : AffineChannelLaw.Word (width p)),
      entry ∈ window ∧ entry.time = record.input.time ∧ actualDownCall i record = some call ∧
      call.1 = record.input.time ∧ entry.time = call.1 ∧ entry.sample = call.2.sample ∧
      0 < (preparedOwnObservation record i).val.val ∧
      (record.output.followers i).downInput = some logged ∧
      (record.output.followers i).down = some cut ∧
      cut.rawComparison.isSome = true ∧ cut.rawComparison = some false ∧
      cut.raw = batchOutput window ∧ cut.raw = none ∧ cut.expectedWord = some word ∧
      (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
        (preparedOwnObservation record i) rate logged).1 =
        ⟨[], seed.completed ++ [seed.pending ++ positives.take (quota p - seed.pending.length), window]⟩ ∧
      satisfies (samples window) word ∧ ∃ other, other ≠ word ∧ satisfies (samples window) other := by
  constructor
  · rintro ⟨entry, call, registers, fields, word, he, het, hc, hct, hec, hes,
      hpos, hlogged, hcut, hcmpSome, hcmp, hraw, hnone, hexpected, hbank, hword, hother⟩
    rw [record_diagnostics] at hlogged hcut
    obtain ⟨logged, hloggedActual, hr⟩ := Option.map_eq_some_iff.mp hlogged
    obtain ⟨cut, hcutActual, hf⟩ := Option.map_eq_some_iff.mp hcut
    subst registers
    subst fields
    have hactual := downCallObservation_reconstructs i record
    change downCallObservation i record = some call at hc
    rw [hc, Option.map_some] at hactual
    refine ⟨entry, decodeCall call, logged, cut, word, he, het, hactual.symm,
      hct, hec, hes, ?_, hloggedActual, hcutActual, hcmpSome, hcmp, hraw, hnone, hexpected, ?_, hword, hother⟩
    · rw [record_observation]
      exact hpos
    · rw [← decodedLoggedBank_actual i record call hc logged]
      exact hbank
  · rintro ⟨entry, call, logged, cut, word, he, het, hc, hct, hec, hes,
      hpos, hlogged, hcut, hcmpSome, hcmp, hraw, hnone, hexpected, hbank, hword, hother⟩
    have hmap := (downCallObservation_reconstructs i record).trans hc
    obtain ⟨code, hcode, heq⟩ := Option.map_eq_some_iff.mp hmap
    subst call
    refine ⟨entry, code, followerStateCode rate logged, cutFields cut, word,
      he, het, hcode, hct, hec, hes, ?_, ?_, ?_, hcmpSome, hcmp, hraw, hnone, hexpected, ?_, hword, hother⟩
    · rw [record_observation] at hpos
      exact hpos
    · rw [record_diagnostics, hlogged]
      rfl
    · rw [record_diagnostics, hcut]
      rfl
    · rw [decodedLoggedBank_actual i record code hcode logged]
      exact hbank

/-- Equality of preparation and final diagnostics follows from the literal
record output equation, including every rejected and failed path. -/
theorem record_preparationDiagnostics (record : Record p rate) (i : Fin (p.m - 1)) :
    record.output.preparation.observeFollower i = record.output.followers i := by
  rcases record with ⟨input, output, houtput⟩
  cases houtput
  rfl

private def secondAmbiguityCodeSet (count : ℕ) : Set (RunDownObservationCode p rate count) :=
  {code | ∃ registers, code.1 = some registers ∧
    let seed := decoderBatchOfCode registers.downBatch
    let positives := positiveCallEntries (observedCalls code)
    let needed := quota p - seed.pending.length
    let window := positives.drop needed
    seed.pending.length < quota p ∧ positives.length = needed + quota p ∧
    window.length = quota p ∧ ∃ k : Fin count,
      code.2 k ∈ completionCodeSet seed positives window}

private theorem decoded_seedBank (seed : ReferencePrelaunchFollower.State p rate.eta) :
    decoderBatchOfCode (followerStateCode rate seed).downBatch = seed.downBatch :=
  decoderBatchOfCode_code _

/-- The produced countable observation characterizes the full runtime event
on all inputs; it is not an assumed measurable-record or success facade. -/
private theorem secondDownAmbiguityEvent_eq_preimage (start count : ℕ) (span : start + count ≤ p.T)
    (i : Fin (p.m - 1)) :
    secondDownAmbiguityEvent (rate := rate) start count span i =
      (runDownObservation start count span i) ⁻¹' secondAmbiguityCodeSet count := by
  ext x
  have hinitial := (runDownObservation_eq_actual start count span i x).1
  have hpositives := observedPositives_eq_actual start count span i x
  have hrecords := run_records_eq_ofFn start count span x
  constructor
  · rintro ⟨seed, memory, hs, hn, hcount, hw, entry, record, call, logged, cut, word,
      he, het, hrecord, hc, hct, hec, hes, hpos, hlogged, hcut, hcmpSome, hcmp,
      hraw, hnone, hexpected, hbank, hword, hother⟩
    refine ⟨followerStateCode rate seed, ?_, ?_⟩
    · rw [hinitial, hs]
    · simp only [decoded_seedBank, hpositives]
      refine ⟨hn, hcount, hw, ?_⟩
      rw [hrecords] at hrecord
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp hrecord
      subst record
      refine ⟨k, (completionCodeSet_iff _ _ _
        (⟨prefixInput start k.val (by omega) x,
          ReferenceActivePhysicalStep.step (prefixInput start k.val (by omega) x), rfl⟩ :
          Record p rate) i).mpr ?_⟩
      exact ⟨entry, call, logged, cut, word, he, het, hc, hct, hec, hes, hpos,
        hlogged, hcut, hcmpSome, hcmp, hraw, hnone, hexpected, hbank, hword, hother⟩
  · rintro ⟨registers, hs, hn, hcount, hw, k, hk⟩
    rw [hinitial] at hs
    cases hconfig : x.val.1.followers i with
    | dagger => simp only [hconfig, reduceCtorEq] at hs
    | ordinary seed memory =>
        simp only [hconfig, Option.some.injEq] at hs
        subst registers
        simp only [decoded_seedBank, hpositives] at hn hcount hw hk
        have hlocal := (completionCodeSet_iff seed.downBatch _ _
          (⟨prefixInput start k.val (by omega) x,
            ReferenceActivePhysicalStep.step (prefixInput start k.val (by omega) x), rfl⟩ :
            Record p rate) i).mp hk
        obtain ⟨entry, call, logged, cut, word, he, het, hc, hct, hec, hes, hpos,
          hlogged, hcut, hcmpSome, hcmp, hraw, hnone, hexpected, hbank, hword, hother⟩ := hlocal
        refine ⟨seed, memory, hconfig, hn, hcount, hw, entry, _, call, logged, cut, word,
          he, het, ?_, hc, hct, hec, hes, hpos, hlogged, hcut, hcmpSome, hcmp,
          hraw, hnone, hexpected, hbank, hword, hother⟩
        rw [hrecords]
        exact List.mem_ofFn.mpr ⟨k, rfl⟩

theorem measurableSet_secondDownAmbiguityEvent (start count : ℕ) (span : start + count ≤ p.T)
    (i : Fin (p.m - 1)) :
    MeasurableSet (secondDownAmbiguityEvent (p := p) (rate := rate) start count span i) := by
  rw [secondDownAmbiguityEvent_eq_preimage]
  exact (Set.to_countable (secondAmbiguityCodeSet (p := p) (rate := rate) count)).measurableSet.preimage
    (measurable_runDownObservation start count span i)

/-- Empty horizons keep their real final state and have no actual calls. -/
theorem zero_horizon (start : ℕ) (span : start + 0 ≤ p.T)
    (i : Fin (p.m - 1)) (x : ActiveRunInput (p := p) (rate := rate) start) :
    observedCalls (runDownObservation start 0 span i x) = [] ∧
    (runOfInput start 0 span x).finalState = x.val.1 ∧
    x ∉ secondDownAmbiguityEvent start 0 span i := by
  refine ⟨rfl, ReferenceActivePhysicalHorizon.run_zero_final _ _ _ _ _ _ _, ?_⟩
  rw [secondDownAmbiguityEvent_eq_preimage]
  rintro ⟨_, _, _, _, _, k, _⟩
  exact Fin.elim0 k

/-- Every actual call retains its original time and the focal channel sample.
The selection bit is the row's literal DOWN selector, including false cases. -/
theorem actualDownCall_fields (record : Record p rate) (i : Fin (p.m - 1))
    (call : Call p) (hcall : actualDownCall i record = some call) :
    call.1 = record.input.time ∧
    call.2.sample = (record.input.row.2 record.input.time).2 (0, i) ∧
    (call.2.selected = true ↔
      ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time) := by
  classical
  cases hconfig : preparedChoiceConfiguration record i with
  | dagger => simp only [actualDownCall, hconfig, reduceCtorEq] at hcall
  | ordinary state memory =>
      have heq := Option.some.inj
        ((actualDownCall_ordinary record i state memory hconfig).symm.trans hcall)
      subst call
      rw [record_row, preparedChoiceTime_eq_recordTime]
      refine ⟨rfl, rfl, ?_⟩
      simp only [ActiveFollowerDownAcceptance.currentRoundInput,
        ActiveFollowerDownAcceptance.downSelected, decide_eq_true_eq]

/-- Only a selected positive DOWN call may use the selected-follower helper
`originalDownSample`; administrative calls still retain their focal sample. -/
theorem actualDownCall_sample_original_of_eligible (record : Record p rate)
    (i : Fin (p.m - 1)) (call : Call p)
    (hcall : actualDownCall i record = some call) (hpositive : eligible call.2) :
    call.2.sample = ReferenceDownPhysicalHashRule.originalDownSample record.input := by
  have hfields := actualDownCall_fields record i call hcall
  have hselected := (hfields.2.2).mp hpositive.1
  rw [hfields.2.1, ReferenceDownPhysicalHashRule.originalDownSample,
    ReferenceActivePhysicalStep.upSenderIndex, CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw,
    hselected.2]

private theorem positive_entry_origin (i : Fin (p.m - 1)) (records : List (Record p rate))
    (e : Entry p.T (width p)) (he : e ∈ actualDownPositives i records) :
    ∃ (record : Record p rate) (call : Call p),
      record ∈ records ∧ actualDownCall i record = some call ∧ eligible call.2 ∧
      e = ⟨call.1, call.2.sample⟩ := by
  classical
  obtain ⟨call, hcall, hentry⟩ := List.mem_flatMap.mp he
  obtain ⟨record, hrecord, hcall⟩ := List.mem_filterMap.mp hcall
  have hpositive : eligible call.2 := by
    by_contra hbad
    simp only [positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
      hbad, ↓reduceIte, List.not_mem_nil] at hentry
  refine ⟨record, call, hrecord, hcall, hpositive, ?_⟩
  simpa only [positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
    hpositive, ↓reduceIte, List.mem_singleton, AffineBatchDecoder.entry] using hentry

/-- A positive entry and any actual call at that same retained time have the
same original focal sample, since the run keeps its original WHOLE rows/J. -/
theorem positiveEntry_sample_of_same_time (start count : ℕ) (span : start + count ≤ p.T)
    (i : Fin (p.m - 1)) (x : ActiveRunInput (p := p) (rate := rate) start)
    (e : Entry p.T (width p))
    (he : e ∈ actualDownPositives i (runOfInput start count span x).records)
    (record : Record p rate) (hrecord : record ∈ (runOfInput start count span x).records)
    (call : Call p) (hcall : actualDownCall i record = some call)
    (htime : e.time = record.input.time) : e.sample = call.2.sample := by
  obtain ⟨origin, originalCall, horigin, hocall, _, heq⟩ := positive_entry_origin i _ e he
  have hsource := ReferenceActivePhysicalHorizon.run_record_inputs
    x.val.1 x.val.2.1 x.val.2.2.1 x.val.2.2.2 start count span x.property origin horigin
  have htarget := ReferenceActivePhysicalHorizon.run_record_inputs
    x.val.1 x.val.2.1 x.val.2.2.1 x.val.2.2.2 start count span x.property record hrecord
  have ho := actualDownCall_fields origin i originalCall hocall
  have ht := actualDownCall_fields record i call hcall
  have htimeOrigin : e.time = origin.input.time := (congrArg Entry.time heq).trans ho.1
  have hsample : e.sample = (origin.input.row.2 origin.input.time).2 (0, i) :=
    (congrArg Entry.sample heq).trans ho.2.1
  rw [hsample, ht.2.1]
  change ((origin.input.rows origin.input.selected).2 origin.input.time).2 (0, i) =
    ((record.input.rows record.input.selected).2 record.input.time).2 (0, i)
  rw [hsource.1, hsource.2.1, htarget.1, htarget.2.1, ← htimeOrigin, htime]

private theorem finishFollower_diagnostic_pair
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p) :
    ((ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput,
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).down) =
    match prepared.configuration with
    | .dagger => (none, none)
    | .ordinary state _ =>
        let recorded := ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation state
        (recorded.downInput, recorded.down) := by
  cases hconfig : prepared.configuration with
  | dagger => simp only [ReferenceActivePhysicalStep.finishFollower, hconfig]
  | ordinary state memory =>
      simp only [ReferenceActivePhysicalStep.finishFollower, hconfig]
      cases hr : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation state).result with
      | error failure => rfl
      | ok post =>
          dsimp only
          cases hf : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
            prepared.time observation state memory post with
          | error failure => rfl
          | ok next => cases next; rfl

private theorem recordFollower_cut_identity
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (active : activation.val ≤ time.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hlogged : (ReferenceActivePhysicalStep.recordFollower view i row activation time active arm
      observation state).downInput = some logged)
    (hcut : (ReferenceActivePhysicalStep.recordFollower view i row activation time active arm
      observation state).down = some cut) :
    cut = ReferenceDownReception.referenceDownCut p view i row time observation rate logged := by
  classical
  by_cases hstatus : state.status = .unoccupied
  · simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hstatus] at hlogged hcut
    cases hlog : ActiveFollowerLogging.checkedLogging i row activation time (arm, observation) state with
    | error failure => simp only [hlog, reduceCtorEq] at hlogged
    | ok actualLogged =>
        simp only [hlog, Option.some.injEq] at hlogged hcut
        subst logged
        exact hcut.symm
  · simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hstatus, reduceCtorEq] at hlogged

/-- Logged input and cut are from the SAME actual runtime receiver operation,
even when consumption or a later finishing operation fails. -/
theorem record_downCut_eq_actual (record : Record p rate) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hlogged : (record.output.followers i).downInput = some logged)
    (hcut : (record.output.followers i).down = some cut) :
    cut = ReferenceDownReception.referenceDownCut p record.output.preparation.coordinator.downView
      i record.input.row record.input.time (preparedOwnObservation record i) rate logged := by
  rw [← record_preparationDiagnostics record i] at hlogged hcut
  have hp := finishFollower_diagnostic_pair record.output.preparation.coordinator.downView
    (record.output.preparation.followers.followers i) (preparedOwnObservation record i)
  change ((record.output.preparation.observeFollower i).downInput,
    (record.output.preparation.observeFollower i).down) = _ at hp
  cases hconfig : (record.output.preparation.followers.followers i).configuration with
  | dagger =>
      rw [hconfig] at hp
      have hnone := congrArg Prod.fst hp
      rw [hlogged] at hnone
      cases hnone
  | ordinary state memory =>
      rw [hconfig] at hp
      have hl := (congrArg Prod.fst hp).symm.trans hlogged
      have hc := (congrArg Prod.snd hp).symm.trans hcut
      have heq := recordFollower_cut_identity _ _ _ _ _ _ _ _ state logged cut hl hc
      rw [(record.output.preparation.follower_alignment i).1,
        (record.output.preparation.follower_alignment i).2.1,
        (record.output.preparation.follower_alignment i).2.2.1] at heq
      exact heq

private theorem referenceDownCut_acceptance_eq
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (logged : ReferencePrelaunchFollower.State p rate.eta) :
    (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).ordinaryAcceptance =
      ReferenceDownReception.ordinaryLocalAcceptanceTest p rate time logged
        (ReferenceDownReception.ordinaryParse p rate
          (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).raw) := by
  classical
  unfold ReferenceDownReception.referenceDownCut
  split
  · split
    · split
      · split
        · split
          · dsimp only
            split <;> rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

/-- NONE is never ordinarily accepted by an actual retained DOWN cut. This
is separate from admissibility of the hypothetical consistent awaited word. -/
theorem record_raw_none_not_accepted (record : Record p rate) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hlogged : (record.output.followers i).downInput = some logged)
    (hcut : (record.output.followers i).down = some cut) (hraw : cut.raw = none) :
    ¬ cut.ordinaryAcceptance := by
  have heq := record_downCut_eq_actual record i logged cut hlogged hcut
  have haccept := referenceDownCut_acceptance_eq
    record.output.preparation.coordinator.downView i record.input.row record.input.time
      (preparedOwnObservation record i) logged
  rw [← heq, hraw] at haccept
  rw [haccept]
  exact not_false

/-- The accepted actual launched first-live branch obtains this Borel target.
All original conditional inputs and endpoint selectors remain explicit; the
count selector stays after the existential actual seed and its equality. -/
theorem ofActualLaunchedBoundary_mem_secondDownAmbiguityEvent :
    ∀ {p : ConstructorDimensions.Parameters}
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (boundary : ReferenceInitializationRun.Boundary p)
    (hboundary : boundary.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock boundary hboundary))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock boundary hboundary) actual boundary past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      boundary hboundary i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          boundary hboundary).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          boundary hboundary)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      boundary hboundary i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock boundary hboundary) source rewards actual.C_star
      actual.C_h (ActualInitializationRun.foldBlock p rate
        (ReferenceInitializationRun.nextBlock boundary hboundary) source rewards actual)).disposition =
          .launched launch learnerSeed)
    (count : ℕ)
    (span : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock boundary hboundary) + count ≤ p.T),
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate C_star C_h
      boundary hboundary actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let rows := source.1.2
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let start := BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock boundary hboundary)
    let mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun j => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
        launch learnerSeed hlaunched j
    ∀ (b : ℕ) (hb : b ≤ count)
    (_hwindow : b ≤ (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span mode).records).length)
    (rB : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (qB : CoordinatorLiveServiceFinish.OwnedRegisters rB)
    (baseB : Fin (p.m - 1) → ℕ)
    (_hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b
      ((Nat.add_le_add_left hb start).trans span) mode).finalState.coordinator =
      .live rB qB baseB)
    (i : Fin (p.m - 1))
    (sB : ReferencePrelaunchFollower.State p rate.eta)
    (memoryB : ActiveFollowerLifecycle.LocalMemory p)
    (_hfocal : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b
      ((Nat.add_le_add_left hb start).trans span) mode).finalState.followers i =
      .ordinary sB memoryB)
    (_hnone : sB.lastDown = none),
    let Rb := ReferenceActivePhysicalHorizon.run initial rows J rewards start b
      ((Nat.add_le_add_left hb start).trans span) mode
    let positives := ReferenceFollowerDownDecoderReplay.actualDownPositives i Rb.records
    ∃ (seed : ReferencePrelaunchFollower.State p rate.eta)
      (seedMemory : ActiveFollowerLifecycle.LocalMemory p),
      initial.followers i = .ordinary seed seedMemory ∧
      ∀ (_hcount : positives.length =
        (AffineBatchDecoder.quota p - seed.downBatch.pending.length) + AffineBatchDecoder.quota p),
        (⟨(initial, rows, J, rewards), mode⟩ : ActiveRunInput (p := p) (rate := rate) start) ∈
          secondDownAmbiguityEvent start b ((Nat.add_le_add_left hb start).trans span) i := by
  intro p source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
    launch learnerSeed hlaunched count span
    initial rows J start mode b hb hwindow rB qB baseB hcoord i sB memoryB hfocal hnone Rb positives
  obtain ⟨seed, seedMemory, hseed, hbranch⟩ :=
    ReferenceFirstDownAwaitedAmbiguity.ofActualLaunchedBoundary_first_down_second_awaited_ambiguity
      source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
      launch learnerSeed hlaunched count span b hb hwindow rB qB baseB hcoord i sB memoryB hfocal hnone
  have hseedBank := ReferenceFollowerDecoderChronology.ofActualLaunchedBoundary_downBatchSeed
    source rewards rate C_star C_h boundary hboundary actual past hr hdown hclean hforce
    launch learnerSeed hlaunched i
  obtain ⟨actualSeed, actualMemory, hactual, _, hwell, _, _⟩ := hseedBank
  have hsame := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hseed.symm.trans hactual)
  have hn : seed.downBatch.pending.length < quota p := by
    rw [hsame.1]
    exact hwell.1
  refine ⟨seed, seedMemory, hseed, ?_⟩
  intro hcount
  obtain ⟨hlen, hword, _horigins, hrawNone, hother,
    entry, record, call, logged, cut, he, het, hrecord, hc, hct, hec, hpos,
    _hprepLog, _hprepCut, hlogged, hcut, hcmpSome, hcmp, hraw, hexpected, hbank, _hparse, _haccept⟩ :=
      hbranch hcount
  let x : ActiveRunInput (p := p) (rate := rate) start := ⟨(initial, rows, J, rewards), mode⟩
  have hsample : entry.sample = call.2.sample :=
    positiveEntry_sample_of_same_time start b ((Nat.add_le_add_left hb start).trans span) i x
      entry (List.mem_of_mem_drop he) record hrecord call hc het
  refine ⟨seed, seedMemory, hseed, hn, hcount, hlen, entry, record, call, logged, cut,
    CoordinatorLocalArmChoice.storedDownFlatWord rB.payload i,
    he, het, hrecord, hc, hct, hec, hsample, hpos, hlogged, hcut, hcmpSome, hcmp,
    hraw, hraw.trans hrawNone, hexpected, hbank, ?_, hother⟩
  exact (satisfies_samples_iff _ _).mpr hword

end Bandits.Support.ReferenceDownCompletedAmbiguityMeasurability

end
