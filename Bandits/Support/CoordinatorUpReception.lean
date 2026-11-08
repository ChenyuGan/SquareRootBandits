/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.AffineBatchDecoder
public import Bandits.Support.AffineChannelLaw
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.CoordinatorCollectionLedger
public import Bandits.Support.OrdinaryMessageCodec
public import Bandits.Support.PublicDiscreteDraws

import Lean.Elab.Tactic.Omega

/-!
# Coordinator UP reception

This is the coordinator's local UP reception operation from
`sources/zip4/manuscript/06_interruptions.tex:277-283`, using the positive-only
affine decoder in `sources/zip4/manuscript/05_binary_transport.tex:23-48`,
the codec acceptance rule in `sources/zip4/manuscript/06_interruptions.tex:123-177`,
and the local domain policy in
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

The operation consumes only the stage-(1) collection ledger, its persistent
per-follower UP decoder bank, the public slot and selected follower, the public
current affine sample, the source round, and the coordinator's own rounded
observation. It does not receive a sent word, a follower reply, collision
indicators, other observations, or omniscient registers. Its output is local
deterministic state; it makes no reachability, authenticity, provenance,
probability, or manuscript-lemma closure claim.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.CoordinatorUpReception

open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.PublicDiscreteDraws

/-- One persistent directed UP decoder state for every finite follower label. -/
abbrev UpDecoderBank (p : ConstructorDimensions.Parameters) :=
  Fin (p.m - 1) → AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)

/-- Initially every directed UP channel has the source's empty batch. This
initializer is separate from reception and is never used to reset a carried
bank at an assignment start or cutoff. -/
def initialUpDecoderBank (p : ConstructorDimensions.Parameters) : UpDecoderBank p :=
  fun _ => AffineBatchDecoder.initial p

/-- The state invariant maintained by one actual affine decoder channel. -/
def decoderStateWellFormed (p : ConstructorDimensions.Parameters)
    (s : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) : Prop :=
  s.pending.length < AffineBatchDecoder.quota p ∧
    ∀ batch, batch ∈ s.completed → batch.length = AffineBatchDecoder.quota p

/-- The bank carries all channels across assignment boundaries and cutoffs. -/
def decoderBankWellFormed (p : ConstructorDimensions.Parameters)
    (bank : UpDecoderBank p) : Prop :=
  ∀ i, decoderStateWellFormed p (bank i)

/-- Executable local-domain check for the existing UP decoder bank. -/
def decoderBankCheck (p : ConstructorDimensions.Parameters)
    (bank : UpDecoderBank p) : Bool := by
  classical
  exact decide (decoderBankWellFormed p bank)

theorem decoderBankCheck_eq_true_iff (p : ConstructorDimensions.Parameters)
    (bank : UpDecoderBank p) :
    decoderBankCheck p bank = true ↔ decoderBankWellFormed p bank := by
  simp [decoderBankCheck]

theorem initialUpDecoderBank_wellFormed (p : ConstructorDimensions.Parameters) :
    decoderBankWellFormed p (initialUpDecoderBank p) := by
  intro i
  constructor
  · simp [initialUpDecoderBank,
      AffineBatchDecoder.initial, AffineBatchDecoder.quota_pos]
  · intro batch hbatch
    simp [initialUpDecoderBank, AffineBatchDecoder.initial] at hbatch

theorem initialUpDecoderBank_check (p : ConstructorDimensions.Parameters) :
    decoderBankCheck p (initialUpDecoderBank p) = true :=
  (decoderBankCheck_eq_true_iff p _).2 (initialUpDecoderBank_wellFormed p)

/-- The actual five-block source width, expressed through the accepted codec. -/
theorem width_eq_codec_width (p : ConstructorDimensions.Parameters) (eta : ℝ) :
    AffineBatchDecoder.width p =
      5 * OrdinaryMessageCodec.fieldWidth
        (CoordinatorCollectionLedger.codecParams p eta).T
        (CoordinatorCollectionLedger.codecParams p eta).D := rfl

/-- The decoder's actual quota is the manuscript's `width + clog₂(4 d T N²)`. -/
theorem quota_eq_source (p : ConstructorDimensions.Parameters) :
    AffineBatchDecoder.quota p =
      5 * OrdinaryMessageCodec.fieldWidth p.T (ConstructorDimensions.D p) +
        Nat.clog 2
          (4 * (p.m - 1) * p.T * (ConstructorDimensions.N p) ^ 2) := rfl

/-- The source's rounded scalar observation, represented by its exact finite
grid index in `0,...,D`. -/
def roundedObservationValue (p : ConstructorDimensions.Parameters)
    (y : Fin (ConstructorDimensions.D p + 1)) : ℝ :=
  (y.val : ℝ) / (ConstructorDimensions.D p : ℝ)

theorem roundedObservationValue_zero (p : ConstructorDimensions.Parameters)
    (y : Fin (ConstructorDimensions.D p + 1)) (hy : y.val = 0) :
    roundedObservationValue p y = 0 := by
  simp [roundedObservationValue, hy]

/-- Exactly the public UP reception inputs. The finite scalar is the
coordinator's already-rounded observation; no private reward or true sent word
is included. `time` is zero-based, and its source round is `time.val + 1`. -/
structure ReceptionInput (p : ConstructorDimensions.Parameters)
    (eta : ℝ) (heta : 0 < eta)
    (hcap : CoordinatorCollectionLedger.sourceLearningCap p eta)
    (n : ℕ)
    (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)) where
  ledger : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn
  upDecoderBank : UpDecoderBank p
  slot : PublicDiscreteDraws.Slot
  selectedFollower : Fin (p.m - 1)
  affineSample : AffineChannelLaw.Sample (AffineBatchDecoder.width p)
  time : Fin p.T
  ownObservation : Fin (ConstructorDimensions.D p + 1)

variable {p : ConstructorDimensions.Parameters} {eta : ℝ} {heta : 0 < eta}
  {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
  {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}

/-- The source gate: collection has begun, the public slot is UP, and the
selected follower is still in the ledger's current pending set `P`. -/
def receptionGate (input : ReceptionInput p eta heta hcap n hn) : Prop :=
  input.ledger.cutoff ≤ CoordinatorCollectionLedger.sourceRound input.time ∧
    input.slot = PublicDiscreteDraws.upSlot ∧
    input.selectedFollower ∈ input.ledger.pending

/-- The one-round affine decoder input. The public gate selects the channel;
only the coordinator's own rounded scalar controls positive-only appending. -/
def roundInput (input : ReceptionInput p eta heta hcap n hn) :
    AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p) := by
  classical
  exact {
    selected := decide (receptionGate input)
    receiverEnabled := true
    sample := input.affineSample
    roundedReward := roundedObservationValue p input.ownObservation
  }

theorem roundInput_selected_iff_gate
    (input : ReceptionInput p eta heta hcap n hn) :
    (roundInput input).selected = true ↔ receptionGate input := by
  classical
  simp [roundInput]

/-- A one-step trace adapter: the decoder reads only the supplied current time. -/
def traceAt (input : ReceptionInput p eta heta hcap n hn) :
    AffineBatchDecoder.Trace p := fun _ => roundInput input

/-- Run the existing decoder on the selected follower's carried UP batch. -/
def decoderTransition (input : ReceptionInput p eta heta hcap n hn) :=
  AffineBatchDecoder.decodeStep p (traceAt input)
    (input.upDecoderBank input.selectedFollower) input.time

/-- Convert the raw flat decoder word through the exact accepted codec
equivalence, then invoke the existing UP parser at the ledger's codec params. -/
def parseDecoderOutput
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) :
    Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p eta)) :=
  OrdinaryMessageCodec.parseUp (CoordinatorCollectionLedger.codecParams p eta)
    (raw.map (OrdinaryMessageCodec.wordEquivFlat
      (CoordinatorCollectionLedger.codecParams p eta)).symm)

/-- The codec's literal all-zero UP placeholder as an admissible UP record. -/
def placeholderUpRecord (p : ConstructorDimensions.Parameters) (eta : ℝ) :
    OrdinaryMessageCodec.UpRecord (CoordinatorCollectionLedger.codecParams p eta) :=
  ⟨OrdinaryMessageCodec.upPlaceholder, Or.inl rfl⟩

/-- The all-zero structured five-block word. -/
def zeroCodecWord (codec : OrdinaryMessageCodec.CodecParams) :
    OrdinaryMessageCodec.Word codec := fun _ _ => 0

/-- The all-zero flat affine word of a fixed width. -/
def zeroFlatWord (B : ℕ) : AffineChannelLaw.Word B := fun _ => 0

theorem encodeUp_placeholder_eq_zero (p : ConstructorDimensions.Parameters) (eta : ℝ) :
    OrdinaryMessageCodec.encodeUp (CoordinatorCollectionLedger.codecParams p eta)
      (placeholderUpRecord p eta) =
        zeroCodecWord (CoordinatorCollectionLedger.codecParams p eta) := by
  funext b i
  fin_cases b <;>
    simp [placeholderUpRecord, OrdinaryMessageCodec.encodeUp,
      OrdinaryMessageCodec.encodeFive, OrdinaryMessageCodec.fiveField,
      OrdinaryMessageCodec.encodeField, OrdinaryMessageCodec.upPlaceholder,
      zeroCodecWord]

theorem wordEquivFlat_symm_zero (codec : OrdinaryMessageCodec.CodecParams) :
    (OrdinaryMessageCodec.wordEquivFlat codec).symm
        (zeroFlatWord (5 * OrdinaryMessageCodec.fieldWidth codec.T codec.D)) =
      zeroCodecWord codec := by
  funext b i
  change (zeroFlatWord (5 * OrdinaryMessageCodec.fieldWidth codec.T codec.D))
      (finProdFinEquiv (m := 5) (n := OrdinaryMessageCodec.fieldWidth codec.T codec.D)
        (b, i)) = 0
  simp [zeroFlatWord]

theorem parseUp_zero_is_placeholder
    (p : ConstructorDimensions.Parameters) (eta : ℝ) :
    OrdinaryMessageCodec.parseUp (CoordinatorCollectionLedger.codecParams p eta)
        (some (zeroCodecWord (CoordinatorCollectionLedger.codecParams p eta))) =
      some (placeholderUpRecord p eta) := by
  rw [← encodeUp_placeholder_eq_zero p eta]
  exact OrdinaryMessageCodec.parseUp_encode
    (CoordinatorCollectionLedger.codecParams p eta) (placeholderUpRecord p eta)

theorem parseDecoderOutput_zero
    (p : ConstructorDimensions.Parameters) (eta : ℝ) :
    parseDecoderOutput (p := p) (eta := eta)
        (some (zeroFlatWord
          (5 * OrdinaryMessageCodec.fieldWidth
            (CoordinatorCollectionLedger.codecParams p eta).T
            (CoordinatorCollectionLedger.codecParams p eta).D))) =
      some (placeholderUpRecord p eta) := by
  change OrdinaryMessageCodec.parseUp (CoordinatorCollectionLedger.codecParams p eta)
    (some ((OrdinaryMessageCodec.wordEquivFlat
      (CoordinatorCollectionLedger.codecParams p eta)).symm
        (zeroFlatWord
          (5 * OrdinaryMessageCodec.fieldWidth
            (CoordinatorCollectionLedger.codecParams p eta).T
            (CoordinatorCollectionLedger.codecParams p eta).D)))) = _
  rw [wordEquivFlat_symm_zero]
  exact parseUp_zero_is_placeholder p eta

/-- Parse exactly the raw output of this input's actual decoder transition. -/
def parsedDecoderOutput (input : ReceptionInput p eta heta hcap n hn) :=
  parseDecoderOutput (p := p) (eta := eta) (decoderTransition input).2

/-- The existing collection ledger's stage-(2) result on the actual parsed raw
decoder output. -/
def ledgerDecodeResult (input : ReceptionInput p eta heta hcap n hn) :=
  CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower
    (parsedDecoderOutput input)

/-- The selected channel receives its actual new decoder state; every other
channel remains the carried state. -/
def decoderBankAfter (input : ReceptionInput p eta heta hcap n hn) :
    UpDecoderBank p :=
  Function.update input.upDecoderBank input.selectedFollower
    (decoderTransition input).1

theorem decoderBankAfter_unselected
    (input : ReceptionInput p eta heta hcap n hn)
    (i : Fin (p.m - 1)) (hi : i ≠ input.selectedFollower) :
    decoderBankAfter input i = input.upDecoderBank i := by
  simp [decoderBankAfter, hi]

/-- The operation's checked local input domain. It repeats the ledger's
positive-sigma field check explicitly, then checks the existing decode phase,
one-based source time, and coordinator-owned decoder-bank bounds. -/
def receptionInputDomain (input : ReceptionInput p eta heta hcap n hn) : Prop :=
  CoordinatorCollectionLedger.validLedgerCheck input.ledger = true ∧
    1 ≤ input.ledger.sigma ∧
    input.ledger.phase = CoordinatorCollectionLedger.Phase.started ∧
    1 ≤ input.ledger.cutoff ∧
    input.ledger.cutoff ≤ input.ledger.cursor ∧
    input.ledger.cursor ≤ p.T ∧
    input.ledger.cursor = CoordinatorCollectionLedger.sourceRound input.time ∧
    decoderBankCheck p input.upDecoderBank = true

/-- Executable check of the local data needed before the reception transition. -/
def receptionInputCheck (input : ReceptionInput p eta heta hcap n hn) : Bool := by
  classical
  exact decide (receptionInputDomain input)

theorem receptionInputCheck_eq_true_iff
    (input : ReceptionInput p eta heta hcap n hn) :
    receptionInputCheck input = true ↔ receptionInputDomain input := by
  simp [receptionInputCheck]

/-- Attach the decoder bank update to the existing ledger's checked result. -/
def packDecodeResult
    (decoded : CoordinatorCollectionLedger.Checked
      (CoordinatorCollectionLedger.Ledger p eta heta hcap n hn))
    (bank : UpDecoderBank p) :
    CoordinatorCollectionLedger.Checked
      (CoordinatorCollectionLedger.Ledger p eta heta hcap n hn × UpDecoderBank p) :=
  match decoded with
  | .success ledger => .success (ledger, bank)
  | .rejected ledger => .rejected (ledger, bank)
  | .invalid => .invalid

/-- Every non-invalid packed ledger result carries exactly the supplied
updated decoder bank. -/
theorem packDecodeResult_output_bank
    (decoded : CoordinatorCollectionLedger.Checked
      (CoordinatorCollectionLedger.Ledger p eta heta hcap n hn))
    (bank : UpDecoderBank p)
    (out : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn × UpDecoderBank p)
    (h : packDecodeResult decoded bank = .success out ∨
      packDecodeResult decoded bank = .rejected out) : out.2 = bank := by
  cases decoded with
  | success ledger =>
      rcases h with hs | hr
      · exact congrArg Prod.snd (Checked.success.inj hs).symm
      · simp [packDecodeResult] at hr
  | rejected ledger =>
      rcases h with hs | hr
      · simp [packDecodeResult] at hs
      · exact congrArg Prod.snd (Checked.rejected.inj hr).symm
  | invalid =>
      simp [packDecodeResult] at h

/-- The checked local UP reception operation. Domain failures are returned as
the ledger's existing `Checked.invalid`; decoder, parser, and local acceptance
rejections remain ordinary `.rejected` outcomes. -/
def receiveUp (input : ReceptionInput p eta heta hcap n hn) :
    CoordinatorCollectionLedger.Checked
      (CoordinatorCollectionLedger.Ledger p eta heta hcap n hn × UpDecoderBank p) := by
  exact if hinput : receptionInputCheck input = true then
    packDecodeResult (ledgerDecodeResult input) (decoderBankAfter input)
  else
    .invalid

/-- An invalid local domain is rejected before a decoder or parsed output is
stored or consumed. -/
theorem receiveUp_invalid_of_domain_check
    (input : ReceptionInput p eta heta hcap n hn)
    (h : receptionInputCheck input = false) :
    receiveUp input = .invalid := by
  simp [receiveUp, h]

/-- The operation's returned ledger is exactly the existing `decodeUp` result
for the parser output obtained from the actual decoder transition. -/
theorem receiveUp_eq_existing_decodeUp
    (input : ReceptionInput p eta heta hcap n hn)
    (h : receptionInputCheck input = true) :
    receiveUp input = packDecodeResult
      (CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower
        (OrdinaryMessageCodec.parseUp
          (CoordinatorCollectionLedger.codecParams p eta)
          ((decoderTransition input).2.map
            (OrdinaryMessageCodec.wordEquivFlat
              (CoordinatorCollectionLedger.codecParams p eta)).symm)))
      (Function.update input.upDecoderBank input.selectedFollower
        (decoderTransition input).1) := by
  simp [receiveUp, h, packDecodeResult, ledgerDecodeResult, parsedDecoderOutput,
    parseDecoderOutput, decoderBankAfter]

/-- Extract the checked ledger and bank invariants from the reception domain. -/
theorem receptionInputDomain_parts
    (input : ReceptionInput p eta heta hcap n hn)
    (h : receptionInputDomain input) :
    CoordinatorCollectionLedger.validLedgerCheck input.ledger = true ∧
      1 ≤ input.ledger.sigma ∧
      input.ledger.phase = CoordinatorCollectionLedger.Phase.started ∧
      1 ≤ input.ledger.cutoff ∧
      input.ledger.cutoff ≤ input.ledger.cursor ∧
      input.ledger.cursor ≤ p.T ∧
      input.ledger.cursor = CoordinatorCollectionLedger.sourceRound input.time ∧
      decoderBankWellFormed p input.upDecoderBank := by
  rcases h with ⟨hl, hsigma, hp, hcut, hle, hT, htime, hbank⟩
  exact ⟨hl, hsigma, hp, hcut, hle, hT, htime,
    (decoderBankCheck_eq_true_iff p input.upDecoderBank).mp hbank⟩

/-- The decoder transition preserves its actual quota and completed-batch
invariant. -/
theorem decoderTransition_state_wellFormed
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input) :
    decoderStateWellFormed p (decoderTransition input).1 := by
  obtain ⟨_, _, _, _, _, _, _, hbank⟩ := receptionInputDomain_parts input hdom
  let tr := traceAt input
  let s := input.upDecoderBank input.selectedFollower
  have hs := hbank input.selectedFollower
  have hstep := AffineBatchDecoder.step_spec p tr s input.time hs.1 hs.2
  constructor
  · simpa [decoderTransition, AffineBatchDecoder.decodeStep, tr, s] using hstep.1
  · intro batch hbatch
    simpa [decoderTransition, AffineBatchDecoder.decodeStep, tr, s] using hstep.2.1 batch hbatch

/-- The existing decoder leaves a well-formed channel unchanged when its
public round input is ineligible. -/
theorem decoderTransition_ineligible
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input)
    (hnot : ¬ AffineBatchDecoder.eligible
      ((traceAt input) input.time)) :
    decoderTransition input =
      (input.upDecoderBank input.selectedFollower, none) := by
  obtain ⟨_, _, _, _, _, _, _, hbank⟩ := receptionInputDomain_parts input hdom
  have hstate := hbank input.selectedFollower
  exact AffineBatchDecoder.decodeStep_ineligible p (traceAt input)
    (input.upDecoderBank input.selectedFollower) input.time hstate.1 hnot

/-- A completed decoder batch clears its pending list independently of whether
the raw solution or subsequent codec parsing succeeds. -/
theorem decoderTransition_decision_clears
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hdecision : (decoderTransition input).2 = some word) :
    (decoderTransition input).1.pending = [] ∧
      ∃ batch, batch ∈ (decoderTransition input).1.completed ∧
        batch.length = AffineBatchDecoder.quota p := by
  obtain ⟨_, _, _, _, _, _, _, hbank⟩ := receptionInputDomain_parts input hdom
  let tr := traceAt input
  let s := input.upDecoderBank input.selectedFollower
  have hs := hbank input.selectedFollower
  have houtput : AffineBatchDecoder.stepOutput p tr s input.time = some word := by
    change (AffineBatchDecoder.decodeStep p (traceAt input)
      (input.upDecoderBank input.selectedFollower) input.time).2 = some word at hdecision
    simpa only [tr, s, AffineBatchDecoder.decodeStep] using hdecision
  have hfull := (AffineBatchDecoder.stepOutput_eq_some_iff p tr s input.time word).mp houtput
  have heligible : AffineBatchDecoder.eligible (tr input.time) := by
    have hpendinglt : s.pending.length < AffineBatchDecoder.quota p := by
      simpa [s] using hs.1
    by_contra hnot
    simp [AffineBatchDecoder.positiveAt, hnot] at hfull
    omega
  have hsize :
      (s.pending ++ AffineBatchDecoder.positiveAt p tr input.time).length =
        AffineBatchDecoder.quota p := by
    have hupper :
        (s.pending ++ AffineBatchDecoder.positiveAt p tr input.time).length ≤
          AffineBatchDecoder.quota p := by
      simp [AffineBatchDecoder.positiveAt, heligible]
      have hpendinglt : s.pending.length < AffineBatchDecoder.quota p := by
        simpa [s] using hs.1
      omega
    exact Nat.le_antisymm hupper hfull.1
  have hpending : s.pending.length + 1 = AffineBatchDecoder.quota p := by
    simpa [AffineBatchDecoder.positiveAt, heligible] using hsize
  have hcomplete := AffineBatchDecoder.decodeStep_complete p tr s input.time
    heligible hpending
  have htransition : decoderTransition input =
      (⟨[], s.completed ++ [s.pending ++ [AffineBatchDecoder.entry p tr input.time]]⟩,
        AffineBatchDecoder.batchOutput
          (s.pending ++ [AffineBatchDecoder.entry p tr input.time])) := by
    simpa [decoderTransition, tr, s, AffineBatchDecoder.decodeStep] using hcomplete
  constructor
  · rw [htransition]
  · refine ⟨s.pending ++ [AffineBatchDecoder.entry p tr input.time], ?_, ?_⟩
    · rw [htransition]
      simp
    · simp [List.length_append, hpending]

theorem decoderBankAfter_wellFormed
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input) :
    decoderBankWellFormed p (decoderBankAfter input) := by
  obtain ⟨_, _, _, _, _, _, _, hbank⟩ := receptionInputDomain_parts input hdom
  have hselected := decoderTransition_state_wellFormed input hdom
  intro i
  by_cases hi : i = input.selectedFollower
  · subst i
    simpa [decoderBankAfter] using hselected
  · simpa [decoderBankAfter, hi] using hbank i

/-- Changing a started ledger to the decode-complete phase preserves its
existing local domain check. -/
def decodePhaseCandidate
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn) :
    CoordinatorCollectionLedger.Ledger p eta heta hcap n hn :=
  { l with phase := CoordinatorCollectionLedger.Phase.decoded }

theorem validLedgerCheck_after_decode
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck l = true)
    (hphase : l.phase = CoordinatorCollectionLedger.Phase.started) :
    CoordinatorCollectionLedger.validLedgerCheck (decodePhaseCandidate l) = true := by
  let decoded := decodePhaseCandidate l
  change CoordinatorCollectionLedger.validLedgerCheck decoded = true
  have hsame : CoordinatorCollectionLedger.validLedgerCheck decoded =
      CoordinatorCollectionLedger.validLedgerCheck l := by
    simp [CoordinatorCollectionLedger.validLedgerCheck,
      decodePhaseCandidate,
      CoordinatorCollectionLedger.rawEntryDomainsCheck,
      CoordinatorCollectionLedger.registerDomainsCheck,
      CoordinatorCollectionLedger.startedHistoryCheck,
      CoordinatorCollectionLedger.armPendingCheck,
      CoordinatorCollectionLedger.allFin,
      CoordinatorCollectionLedger.anyFin,
      decoded, hphase]
  rw [hsame]
  exact hvalid

/-- An unparsed output completes the existing ledger decode phase and preserves
all of its data fields. -/
theorem decodeUp_none_rejected
    (input : ReceptionInput p eta heta hcap n hn)
    (h : receptionInputDomain input) :
    CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower none =
      .rejected { input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded } := by
  obtain ⟨hvalid, _, hphase, hcut, hcutCursor, hcursorT, _, _⟩ :=
    receptionInputDomain_parts input h
  have hnext : CoordinatorCollectionLedger.validLedgerCheck
      (show CoordinatorCollectionLedger.Ledger p eta heta hcap n hn from
        { input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded }) = true := by
    change CoordinatorCollectionLedger.validLedgerCheck
      (decodePhaseCandidate input.ledger) = true
    exact validLedgerCheck_after_decode input.ledger hvalid hphase
  have hdecodeInput :
      CoordinatorCollectionLedger.validLedgerCheck input.ledger = true ∧
        input.ledger.phase = CoordinatorCollectionLedger.Phase.started ∧
        1 ≤ input.ledger.cutoff ∧ input.ledger.cutoff ≤ input.ledger.cursor ∧
        input.ledger.cursor ≤ p.T :=
    ⟨hvalid, hphase, hcut, hcutCursor, hcursorT⟩
  simp [CoordinatorCollectionLedger.decodeUp, hdecodeInput, hnext]

/-- A parsed record that fails the ledger's existing UP acceptance predicate
is an ordinary rejection and changes only the ledger phase. -/
theorem decodeUp_unaccepted_rejected
    (input : ReceptionInput p eta heta hcap n hn)
    (h : receptionInputDomain input)
    (M : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p eta))
    (hnot : ¬ CoordinatorCollectionLedger.acceptUpCheck
      input.ledger input.selectedFollower M) :
    CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower (some M) =
      .rejected { input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded } := by
  obtain ⟨hvalid, _, hphase, hcut, hcutCursor, hcursorT, _, _⟩ :=
    receptionInputDomain_parts input h
  have hnext : CoordinatorCollectionLedger.validLedgerCheck
      (show CoordinatorCollectionLedger.Ledger p eta heta hcap n hn from
        { input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded }) = true := by
    change CoordinatorCollectionLedger.validLedgerCheck
      (decodePhaseCandidate input.ledger) = true
    exact validLedgerCheck_after_decode input.ledger hvalid hphase
  have hdecodeInput :
      CoordinatorCollectionLedger.validLedgerCheck input.ledger = true ∧
        input.ledger.phase = CoordinatorCollectionLedger.Phase.started ∧
        1 ≤ input.ledger.cutoff ∧ input.ledger.cutoff ≤ input.ledger.cursor ∧
        input.ledger.cursor ≤ p.T :=
    ⟨hvalid, hphase, hcut, hcutCursor, hcursorT⟩
  simp [CoordinatorCollectionLedger.decodeUp, hdecodeInput, hnot, hnext]

/-- Every successful ledger decode passed the existing literal UP acceptance
test, including cutoff, current pending membership, and current assignment
sigma. -/
theorem decodeUp_success_implies_literal_acceptUp
    (input : ReceptionInput p eta heta hcap n hn)
    (h : receptionInputDomain input)
    (parsed : Option (OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p eta)))
    (out : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (hresult : CoordinatorCollectionLedger.decodeUp input.ledger
      input.selectedFollower parsed = .success out) :
    ∃ M, parsed = some M ∧
      OrdinaryMessageCodec.acceptUp (CoordinatorCollectionLedger.codecParams p eta)
        input.ledger.cutoff input.ledger.cursor input.selectedFollower.val
        (CoordinatorCollectionLedger.pendingNaturalLabels input.ledger)
        input.ledger.sigma M := by
  obtain ⟨hvalid, _, hphase, hcut, hcutCursor, hcursorT, _, _⟩ :=
    receptionInputDomain_parts input h
  have hdecodeInput :
      CoordinatorCollectionLedger.validLedgerCheck input.ledger = true ∧
        input.ledger.phase = CoordinatorCollectionLedger.Phase.started ∧
        1 ≤ input.ledger.cutoff ∧ input.ledger.cutoff ≤ input.ledger.cursor ∧
        input.ledger.cursor ≤ p.T :=
    ⟨hvalid, hphase, hcut, hcutCursor, hcursorT⟩
  have hnext : CoordinatorCollectionLedger.validLedgerCheck
      (show CoordinatorCollectionLedger.Ledger p eta heta hcap n hn from
        { input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded }) = true := by
    change CoordinatorCollectionLedger.validLedgerCheck
      (decodePhaseCandidate input.ledger) = true
    exact validLedgerCheck_after_decode input.ledger hvalid hphase
  unfold CoordinatorCollectionLedger.decodeUp at hresult
  rw [dite_eq_left hdecodeInput] at hresult
  cases hp : parsed with
  | none => simp [hp, hnext] at hresult
  | some M =>
      by_cases haccept :
          CoordinatorCollectionLedger.acceptUpCheck
            input.ledger input.selectedFollower M
      · exact ⟨M, rfl,
          (CoordinatorCollectionLedger.acceptUpCheck_iff
            input.ledger input.selectedFollower M).mp haccept⟩
      · simp [hp, haccept, hnext] at hresult

/-- If the actual raw decoder has no decision, the existing ledger rejects no
record, advances to `decoded`, and retains exactly the new/old carried batch
bank state. -/
theorem receiveUp_no_raw_decision
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input)
    (hraw : (decoderTransition input).2 = none) :
    receiveUp input = .rejected
      ({ input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded },
        decoderBankAfter input) := by
  have hcheck := (receptionInputCheck_eq_true_iff input).2 hdom
  have hparsed : parsedDecoderOutput input = none := by
    unfold parsedDecoderOutput parseDecoderOutput
    rw [hraw]
    rfl
  have hledger : ledgerDecodeResult input = .rejected
      { input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded } := by
    unfold ledgerDecodeResult
    rw [hparsed]
    exact decodeUp_none_rejected input hdom
  rw [receiveUp_eq_existing_decodeUp input hcheck]
  change packDecodeResult (ledgerDecodeResult input) (decoderBankAfter input) = _
  rw [hledger]
  rfl

/-- A non-UP public slot never contributes to any UP channel. -/
theorem receiveUp_noUp_equation
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input)
    (hslot : input.slot ≠ PublicDiscreteDraws.upSlot) :
    receiveUp input = .rejected
      ({ input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded },
        input.upDecoderBank) := by
  classical
  have hgate : ¬ receptionGate input := by
    rintro ⟨_, hselected, _⟩
    exact hslot hselected
  have hnot : ¬ AffineBatchDecoder.eligible ((traceAt input) input.time) := by
    intro he
    have hselected := he.1
    change decide (receptionGate input) = true at hselected
    exact hgate (of_decide_eq_true hselected)
  have htransition := decoderTransition_ineligible input hdom hnot
  have hraw : (decoderTransition input).2 = none := by
    rw [htransition]
  have hresult := receiveUp_no_raw_decision input hdom hraw
  simpa [decoderBankAfter, htransition] using hresult

/-- A selected follower outside the ledger's current pending set receives no
decoder input and cannot be accepted. -/
theorem receiveUp_nonpending_equation
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input)
    (hnotpending : input.selectedFollower ∉ input.ledger.pending) :
    receiveUp input = .rejected
      ({ input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded },
        input.upDecoderBank) := by
  classical
  have hgate : ¬ receptionGate input := by
    rintro ⟨_, _, hselected⟩
    exact hnotpending hselected
  have hnot : ¬ AffineBatchDecoder.eligible ((traceAt input) input.time) := by
    intro he
    have hselected := he.1
    change decide (receptionGate input) = true at hselected
    exact hgate (of_decide_eq_true hselected)
  have htransition := decoderTransition_ineligible input hdom hnot
  have hraw : (decoderTransition input).2 = none := by
    rw [htransition]
  have hresult := receiveUp_no_raw_decision input hdom hraw
  simpa [decoderBankAfter, htransition] using hresult

/-- A zero rounded coordinator observation leaves the selected UP batch and
ledger data fields unchanged, while completing the existing decode phase. -/
theorem receiveUp_zero_observation_equation
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input)
    (hzero : input.ownObservation.val = 0) :
    receiveUp input = .rejected
      ({ input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded },
        input.upDecoderBank) := by
  have hnot : ¬ AffineBatchDecoder.eligible ((traceAt input) input.time) := by
    intro he
    have hpositive := he.2.2
    change 0 < roundedObservationValue p input.ownObservation at hpositive
    rw [roundedObservationValue_zero p input.ownObservation hzero] at hpositive
    exact (lt_irrefl 0) hpositive
  have htransition := decoderTransition_ineligible input hdom hnot
  have hraw : (decoderTransition input).2 = none := by
    rw [htransition]
  have hresult := receiveUp_no_raw_decision input hdom hraw
  simpa [decoderBankAfter, htransition] using hresult

/-- Parser rejection is a normal local rejection. It advances only the
ledger's decode phase and retains the decoder transition's actual batch state. -/
theorem receiveUp_parser_rejection
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input)
    (hparsed : parsedDecoderOutput input = none) :
    receiveUp input = .rejected
      ({ input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded },
        decoderBankAfter input) := by
  have hcheck := (receptionInputCheck_eq_true_iff input).2 hdom
  have hledger : ledgerDecodeResult input = .rejected
      { input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded } := by
    unfold ledgerDecodeResult
    rw [hparsed]
    exact decodeUp_none_rejected input hdom
  rw [receiveUp_eq_existing_decodeUp input hcheck]
  change packDecodeResult (ledgerDecodeResult input) (decoderBankAfter input) = _
  rw [hledger]
  rfl

/-- Literal local acceptance failure is a normal rejection and preserves all
ledger data fields while advancing the decode phase. -/
theorem receiveUp_acceptance_rejection
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input)
    (M : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p eta))
    (hparsed : parsedDecoderOutput input = some M)
    (hnot : ¬ CoordinatorCollectionLedger.acceptUpCheck
      input.ledger input.selectedFollower M) :
    receiveUp input = .rejected
      ({ input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded },
        decoderBankAfter input) := by
  have hcheck := (receptionInputCheck_eq_true_iff input).2 hdom
  have hledger : ledgerDecodeResult input = .rejected
      { input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded } := by
    unfold ledgerDecodeResult
    rw [hparsed]
    exact decodeUp_unaccepted_rejected input hdom M hnot
  rw [receiveUp_eq_existing_decodeUp input hcheck]
  change packDecodeResult (ledgerDecodeResult input) (decoderBankAfter input) = _
  rw [hledger]
  rfl

/-- A successful reception is accepted by the existing literal codec test on
the actual parsed raw decoder word. -/
theorem receiveUp_success_implies_literal_acceptUp
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input)
    (out : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn × UpDecoderBank p)
    (hresult : receiveUp input = .success out) :
    ∃ M, parsedDecoderOutput input = some M ∧
      OrdinaryMessageCodec.acceptUp (CoordinatorCollectionLedger.codecParams p eta)
        input.ledger.cutoff input.ledger.cursor input.selectedFollower.val
        (CoordinatorCollectionLedger.pendingNaturalLabels input.ledger)
        input.ledger.sigma M := by
  have hcheck := (receptionInputCheck_eq_true_iff input).2 hdom
  rw [receiveUp_eq_existing_decodeUp input hcheck] at hresult
  change packDecodeResult
      (CoordinatorCollectionLedger.decodeUp input.ledger input.selectedFollower
        (parsedDecoderOutput input)) (decoderBankAfter input) = .success out at hresult
  cases hdecode : CoordinatorCollectionLedger.decodeUp input.ledger
      input.selectedFollower (parsedDecoderOutput input) with
  | success ledger =>
      exact decodeUp_success_implies_literal_acceptUp input hdom
        (parsedDecoderOutput input) ledger hdecode
  | rejected ledger => simp [packDecodeResult, hdecode] at hresult
  | invalid => simp [packDecodeResult, hdecode] at hresult

/-- The successful literal UP test explicitly supplies the current collection
time, current pending membership, and current assignment sigma. -/
theorem receiveUp_success_acceptance_fields
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input)
    (out : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn × UpDecoderBank p)
    (hresult : receiveUp input = .success out) :
    ∃ M, parsedDecoderOutput input = some M ∧
      input.ledger.cutoff ≤ input.ledger.cursor ∧
      input.selectedFollower ∈ input.ledger.pending ∧
      M.val.sigma = input.ledger.sigma := by
  obtain ⟨M, hparsed, haccept⟩ :=
    receiveUp_success_implies_literal_acceptUp input hdom out hresult
  refine ⟨M, hparsed, haccept.1, ?_, haccept.2.2⟩
  exact (CoordinatorCollectionLedger.pendingNaturalLabels_mem_iff
    input.ledger input.selectedFollower).mp haccept.2.1

/-- The checked reception input explicitly includes the ledger's positive
current assignment sigma domain. -/
theorem ledgerSigma_pos_of_receptionDomain
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input) : 1 ≤ input.ledger.sigma :=
  (receptionInputDomain_parts input hdom).2.1

/-- The parsed initial all-zero UP placeholder fails the actual local
acceptance test for every valid collection ledger. -/
theorem placeholder_not_literal_acceptUp
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input) :
    ¬ OrdinaryMessageCodec.acceptUp (CoordinatorCollectionLedger.codecParams p eta)
      input.ledger.cutoff input.ledger.cursor input.selectedFollower.val
      (CoordinatorCollectionLedger.pendingNaturalLabels input.ledger)
      input.ledger.sigma (placeholderUpRecord p eta) := by
  intro haccept
  have hsigma := haccept.2.2
  have hpositive := ledgerSigma_pos_of_receptionDomain input hdom
  simp [placeholderUpRecord, OrdinaryMessageCodec.upPlaceholder] at hsigma
  omega

/-- A flat all-zero raw decoder result parses to the exact existing UP
placeholder, then follows the ordinary acceptance-rejection path. -/
theorem receiveUp_zero_raw_placeholder_rejected
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input)
    (hraw : (decoderTransition input).2 =
      some (zeroFlatWord (AffineBatchDecoder.width p))) :
    receiveUp input = .rejected
      ({ input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded },
        decoderBankAfter input) := by
  have hparsed : parsedDecoderOutput input = some (placeholderUpRecord p eta) := by
    unfold parsedDecoderOutput
    rw [hraw]
    exact parseDecoderOutput_zero p eta
  apply receiveUp_acceptance_rejection input hdom (placeholderUpRecord p eta) hparsed
  intro haccept
  exact placeholder_not_literal_acceptUp input hdom
    ((CoordinatorCollectionLedger.acceptUpCheck_iff
      input.ledger input.selectedFollower (placeholderUpRecord p eta)).mp haccept)

/-- Any ordinary checked output preserves every bank channel other than the
publicly selected follower. -/
theorem receiveUp_preserves_unselected_bank
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input)
    (out : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn × UpDecoderBank p)
    (hresult : receiveUp input = .success out ∨ receiveUp input = .rejected out)
    (i : Fin (p.m - 1)) (hi : i ≠ input.selectedFollower) :
    out.2 i = input.upDecoderBank i := by
  have hcheck := (receptionInputCheck_eq_true_iff input).2 hdom
  rw [receiveUp_eq_existing_decodeUp input hcheck] at hresult
  have hbank : out.2 = decoderBankAfter input := by
    cases hresult with
    | inl hs =>
        exact packDecodeResult_output_bank _ _ out (.inl hs)
    | inr hr =>
        exact packDecodeResult_output_bank _ _ out (.inr hr)
  calc
    out.2 i = decoderBankAfter input i := congrArg (fun bank : UpDecoderBank p => bank i) hbank
    _ = input.upDecoderBank i := decoderBankAfter_unselected input i hi

/-- Every non-invalid operation output retains a well-formed carried decoder
bank, so every completed batch has exactly the actual decoder quota. -/
theorem receiveUp_output_bank_wellFormed
    (input : ReceptionInput p eta heta hcap n hn)
    (hdom : receptionInputDomain input)
    (out : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn × UpDecoderBank p)
    (hresult : receiveUp input = .success out ∨ receiveUp input = .rejected out) :
    decoderBankWellFormed p out.2 := by
  have hcheck := (receptionInputCheck_eq_true_iff input).2 hdom
  rw [receiveUp_eq_existing_decodeUp input hcheck] at hresult
  have hbank : out.2 = decoderBankAfter input := by
    cases hresult with
    | inl hs => exact packDecodeResult_output_bank _ _ out (.inl hs)
    | inr hr => exact packDecodeResult_output_bank _ _ out (.inr hr)
  rw [hbank]
  exact decoderBankAfter_wellFormed input hdom

/-- The result is a deterministic function of the complete supplied local
reception input. No sent word or other receiver's information enters through
an implicit argument or a side channel. -/
theorem receiveUp_determined_by_local_input
    (input input' : ReceptionInput p eta heta hcap n hn)
    (heq : input = input') : receiveUp input = receiveUp input' := by
  cases heq
  rfl

end Bandits.Support.CoordinatorUpReception

end
