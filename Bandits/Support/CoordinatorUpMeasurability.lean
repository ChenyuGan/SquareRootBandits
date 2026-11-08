/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CoordinatorUpReception
public import Bandits.Support.CoordinatorCollectionLedger
public import Bandits.Support.ContinuousLearningRows
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.PublicDiscreteDraws
public import Bandits.Support.AffineBatchDecoder
public import Bandits.Support.AffineChannelLaw
public import Bandits.Support.OrdinaryMessageCodec
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Logic.Encodable.Pi
public import Mathlib.Logic.Equiv.Finset

/-!
# Measurability of the coordinator's actual UP reception operation

The operation-level adapter follows
`sources/zip4/manuscript/05_binary_transport.tex:7-43`,
`sources/zip4/manuscript/06_interruptions.tex:270-283`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:60-84`.
It feeds the coordinator's current accepted row control into the existing
`CoordinatorUpReception.receiveUp`. The ledger, decoder bank, time, and rounded
observation remain explicit inputs over their full countable carriers.
No physical execution, provenance, history, or source-lemma closure is claimed.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.CoordinatorUpMeasurability

open MeasureTheory
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.AffineChannelLaw
open Bandits.Support.CompletePublicTable
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.PublicDiscreteDraws

variable {p : ConstructorDimensions.Parameters}
variable {eta : ℝ} {heta : 0 < eta}
  {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
  {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}

/-! ## Countable codes for the existing discrete registers -/

private theorem countable_finArrow (k : ℕ) {α : Type*} [Countable α] :
    Countable (Fin k → α) := by
  let encα : Encodable α := Encodable.ofCountable α
  let encFunction : Encodable (Fin k → α) :=
    @Encodable.fintypeArrowOfEncodable (Fin k) α inferInstance inferInstance encα
  exact @Encodable.countable (Fin k → α) encFunction

private instance finArrowCountable (k : ℕ) {α : Type*} [Countable α] :
    Countable (Fin k → α) :=
  countable_finArrow k

def assignmentCode (a : CoordinatorCollectionLedger.Assignment p) := a.arm

theorem assignmentCode_injective :
    Function.Injective (assignmentCode (p := p)) := by
  intro a b h
  cases a with
  | mk arm₁ hinj₁ =>
    cases b with
    | mk arm₂ hinj₂ =>
      simp only [assignmentCode] at h
      cases h
      rfl

instance assignmentCountable : Countable (CoordinatorCollectionLedger.Assignment p) :=
  assignmentCode_injective.countable

def cutoffRegisterCode (r : CoordinatorCollectionLedger.CutoffRegister) :=
  (r.score, (r.queue, r.lastService))

theorem cutoffRegisterCode_injective :
    Function.Injective (cutoffRegisterCode) := by
  intro a b h
  cases a with
  | mk as aq ad =>
    cases b with
    | mk bs bq bd =>
      simp only [cutoffRegisterCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl

instance cutoffRegisterCountable : Countable CoordinatorCollectionLedger.CutoffRegister :=
  cutoffRegisterCode_injective.countable

def currentRegisterCode (r : CoordinatorCollectionLedger.CurrentRegister) :=
  (r.queue, r.lastService)

theorem currentRegisterCode_injective :
    Function.Injective (currentRegisterCode) := by
  intro a b h
  cases a with
  | mk aq ad =>
    cases b with
    | mk bq bd =>
      simp only [currentRegisterCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl

instance currentRegisterCountable : Countable CoordinatorCollectionLedger.CurrentRegister :=
  currentRegisterCode_injective.countable

def rawArrivalCode {K T : ℕ} (r : CoordinatorCollectionLedger.RawArrival K T) :=
  (r.arm, (r.round, r.amount))

theorem rawArrivalCode_injective {K T : ℕ} :
    Function.Injective (rawArrivalCode (K := K) (T := T)) := by
  intro a b h
  cases a with
  | mk aa ar av apos =>
    cases b with
    | mk ba br bv bpos =>
      simp only [rawArrivalCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl

instance rawArrivalCountable (K T : ℕ) :
    Countable (CoordinatorCollectionLedger.RawArrival K T) :=
  rawArrivalCode_injective.countable

def decoderEntryCode {T B : ℕ} (e : AffineBatchDecoder.Entry T B) :=
  (e.time, e.sample)

theorem decoderEntryCode_injective {T B : ℕ} :
    Function.Injective (decoderEntryCode (T := T) (B := B)) := by
  intro a b h
  cases a with
  | mk atime asample =>
    cases b with
    | mk btime bsample =>
      simp only [decoderEntryCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl

instance decoderEntryCountable (T B : ℕ) :
    Countable (AffineBatchDecoder.Entry T B) :=
  decoderEntryCode_injective.countable

theorem countable_decoderBatch (T B : ℕ) :
    Countable (List (AffineBatchDecoder.Entry T B)) := by
  infer_instance

def decoderStateCode {T B : ℕ} (s : AffineBatchDecoder.State T B) :=
  (s.pending, s.completed)

theorem decoderStateCode_injective {T B : ℕ} :
    Function.Injective (decoderStateCode (T := T) (B := B)) := by
  intro a b h
  cases a with
  | mk ap ac =>
    cases b with
    | mk bp bc =>
      simp only [decoderStateCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl

instance decoderStateCountable (T B : ℕ) :
    Countable (AffineBatchDecoder.State T B) :=
  decoderStateCode_injective.countable

instance affineSampleCountable (B : ℕ) : Countable (AffineChannelLaw.Sample B) := by
  infer_instance

instance affineSampleMeasurableEq (B : ℕ) : MeasurableEq (AffineChannelLaw.Sample B) where
  measurableSet_diagonal := MeasurableSet.of_discrete

def phaseCode : CoordinatorCollectionLedger.Phase → Fin 3
  | .ready => 0
  | .started => 1
  | .decoded => 2

theorem phaseCode_injective : Function.Injective phaseCode := by
  intro a b h
  cases a <;> cases b <;> simp [phaseCode] at h ⊢

instance phaseCountable : Countable CoordinatorCollectionLedger.Phase :=
  phaseCode_injective.countable

def ledgerCode (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn) :=
  (l.assignment, l.sigma, l.cutoff, l.freezeAt, l.baseScore, l.pending,
    l.cutoffRegisters, l.currentRegisters, l.increment, l.gammaLoc, l.rawBuffer,
    l.enabledHistory, l.cursor, l.phase)

theorem ledgerCode_injective :
    Function.Injective (ledgerCode (p := p) (eta := eta) (heta := heta)
      (hcap := hcap) (n := n) (hn := hn)) := by
  intro a b h
  cases a with
  | mk aa as ac af abs ap acr cur inc gam raw enabled cursor phase =>
    cases b with
    | mk ba bs bc bf bbs bp bcr bcur binc bgam braw benabled bcursor bphase =>
      simp only [ledgerCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl

instance ledgerCountable :
    Countable (CoordinatorCollectionLedger.Ledger p eta heta hcap n hn) :=
  ledgerCode_injective.countable

abbrev UpDecoderBank (p : ConstructorDimensions.Parameters) :=
  CoordinatorUpReception.UpDecoderBank p

instance upDecoderBankCountable : Countable (UpDecoderBank p) := by
  exact countable_finArrow (p.m - 1)

instance ledgerMeasurableSpace :
    MeasurableSpace (CoordinatorCollectionLedger.Ledger p eta heta hcap n hn) := ⊤

instance upDecoderBankMeasurableSpace : MeasurableSpace (UpDecoderBank p) := ⊤

def upFieldsCode (x : OrdinaryMessageCodec.UpFields) :=
  (x.sigma, (x.S, (x.delta, x.q)))

theorem upFieldsCode_injective :
    Function.Injective upFieldsCode := by
  intro a b h
  cases a with
  | mk as aS ad aq =>
    cases b with
    | mk bs bS bd bq =>
      simp only [upFieldsCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      rfl

instance upFieldsCountable : Countable OrdinaryMessageCodec.UpFields :=
  upFieldsCode_injective.countable

instance upRecordCountable (codec : OrdinaryMessageCodec.CodecParams) :
    Countable (OrdinaryMessageCodec.UpRecord codec) := by
  change Countable {x : OrdinaryMessageCodec.UpFields // OrdinaryMessageCodec.upAdmissible codec x}
  exact Subtype.val_injective.countable

def receptionInputCode
    (input : CoordinatorUpReception.ReceptionInput p eta heta hcap n hn) :=
  (input.ledger,
   (input.upDecoderBank,
    (input.slot,
     (input.selectedFollower,
      (input.affineSample, (input.time, input.ownObservation))))))

theorem receptionInputCode_injective :
    Function.Injective (receptionInputCode (p := p) (eta := eta) (heta := heta)
      (hcap := hcap) (n := n) (hn := hn)) := by
  intro a b h
  cases a with
  | mk al ab aslot ai asample atime ay =>
    cases b with
    | mk bl bb bslot bi bsample btime byObs =>
      simp only [receptionInputCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl

instance receptionInputCountable :
    Countable (CoordinatorUpReception.ReceptionInput p eta heta hcap n hn) :=
  receptionInputCode_injective.countable

def checkedOutputCode {α : Type*}
    (result : CoordinatorCollectionLedger.Checked α) : Option (Bool × α) :=
  match result with
  | .success value => some (true, value)
  | .rejected value => some (false, value)
  | .invalid => none

theorem checkedOutputCode_injective {α : Type*} :
    Function.Injective (checkedOutputCode (α := α)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [checkedOutputCode]

instance checkedCountable {α : Type*} [Countable α] :
    Countable (CoordinatorCollectionLedger.Checked α) :=
  checkedOutputCode_injective.countable

instance receptionInputMeasurableSpace :
    MeasurableSpace (CoordinatorUpReception.ReceptionInput p eta heta hcap n hn) := ⊤

instance receptionOutputMeasurableSpace :
    MeasurableSpace (CoordinatorCollectionLedger.Checked
      (CoordinatorCollectionLedger.Ledger p eta heta hcap n hn × UpDecoderBank p)) := ⊤

instance upFieldsMeasurableSpace :
    MeasurableSpace OrdinaryMessageCodec.UpFields := ⊤

instance upRecordMeasurableSpace (codec : OrdinaryMessageCodec.CodecParams) :
    MeasurableSpace (OrdinaryMessageCodec.UpRecord codec) := ⊤

instance affineWordMeasurableSpace (B : ℕ) :
    MeasurableSpace (AffineChannelLaw.Word B) := ⊤

instance rawDecoderOutputMeasurableSpace (B : ℕ) :
    MeasurableSpace (Option (AffineChannelLaw.Word B)) := ⊤

instance parsedDecoderOutputMeasurableSpace (codec : OrdinaryMessageCodec.CodecParams) :
    MeasurableSpace (Option (OrdinaryMessageCodec.UpRecord codec)) := ⊤

/-! ## The row-facing operation adapter -/

abbrev ReceptionLocalInputs (p : ConstructorDimensions.Parameters)
    (eta : ℝ) (heta : 0 < eta)
    (hcap : CoordinatorCollectionLedger.sourceLearningCap p eta)
    (n : ℕ) (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)) :=
  CoordinatorCollectionLedger.Ledger p eta heta hcap n hn ×
    (UpDecoderBank p × (Fin p.T × Fin (ConstructorDimensions.D p + 1)))

/-- Convert the existing selected follower to the accepted `Fin (m - 1)`
channel carrier by preserving its value and transporting its range proof. -/
def selectedFollowerIndex (control : ContinuousLearningRows.TimeControl p) :
    Fin (p.m - 1) :=
  let i := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1
  ⟨i.val, by simpa [PublicDiscreteDraws.followerCount] using i.isLt⟩

theorem selectedFollowerIndex_eq_draw
    (control : ContinuousLearningRows.TimeControl p) :
    selectedFollowerIndex control =
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1 := by
  apply Fin.ext
  rfl

private theorem measurable_selectedFollowerIndex :
    Measurable (fun control : ContinuousLearningRows.TimeControl p =>
      selectedFollowerIndex control) := by
  let convert : Fin (PublicDiscreteDraws.followerCount p.m) → Fin (p.m - 1) :=
    fun i => ⟨i.val, by simpa [PublicDiscreteDraws.followerCount] using i.isLt⟩
  have hconvert : Measurable convert := Measurable.of_discrete
  have hdraw : Measurable (fun control : ContinuousLearningRows.TimeControl p =>
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1) :=
    (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp measurable_fst
  change Measurable (convert ∘ fun control : ContinuousLearningRows.TimeControl p =>
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1)
  exact hconvert.comp hdraw

/-- Convert the sampled zero-based follower index to the accepted affine
channel carrier, whose follower parameter is indexed by `ContinuousLearningRows.d`. -/
def selectedChannelFollower (control : ContinuousLearningRows.TimeControl p) :
    Fin (ContinuousLearningRows.d p) :=
  Fin.cast rfl (selectedFollowerIndex control)

theorem selectedChannelFollower_val (control : ContinuousLearningRows.TimeControl p) :
    (selectedChannelFollower control).val =
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1).val := by
  rfl

private theorem measurable_selectedChannelFollower :
    Measurable (fun control : ContinuousLearningRows.TimeControl p =>
      selectedChannelFollower control) := by
  have hcast : Measurable (fun i : Fin (p.m - 1) =>
      Fin.cast rfl i) := Measurable.of_discrete
  change Measurable ((fun i : Fin (p.m - 1) =>
    Fin.cast rfl i) ∘ selectedFollowerIndex)
  exact hcast.comp measurable_selectedFollowerIndex

/-- The source follower label corresponding to the current control's existing
zero-based selected-follower draw. The reception and channel APIs retain the
same zero-based index. -/
def selectedSourcePlayer (control : ContinuousLearningRows.TimeControl p) : Fin p.m :=
  PublicDiscreteDraws.followerPlayer p.two_le_m
    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1)

theorem selectedSourcePlayer_val (control : ContinuousLearningRows.TimeControl p) :
    (selectedSourcePlayer control).val =
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1).val + 1 :=
  PublicDiscreteDraws.followerPlayer_val p.two_le_m _

/-- Construct the actual operation input from one current time control and the
supplied inputs discrete registers. The channel sample is looked up at the UP
direction and the follower selected from this same control. -/
def receptionInputAtControl
    (control : ContinuousLearningRows.TimeControl p)
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) :
    CoordinatorUpReception.ReceptionInput p eta heta hcap n hn :=
  let selected := selectedFollowerIndex control
  { ledger := inputs.1
    upDecoderBank := inputs.2.1
    slot := PublicDiscreteDraws.slotDraw control.1
    selectedFollower := selected
    affineSample := control.2 (1, selectedChannelFollower control)
    time := inputs.2.2.1
    ownObservation := inputs.2.2.2 }

/-- Construct the reception input from the coordinator's own actual complete
row at time `t`. -/
def receptionInputAtRow
    (row : CompletePublicTable.CompleteRow p) (inputs : ReceptionLocalInputs p eta heta hcap n hn)
    (t : Fin p.T) : CoordinatorUpReception.ReceptionInput p eta heta hcap n hn :=
  receptionInputAtControl (row.2 t) inputs

/-- Specialize the same adapter to the fixed coordinator-selected row `q` of
the complete public table. -/
def receptionInputAtSelectedRow
    (rows : CompletePublicTable.CompleteRows p) (q : Fin (ConstructorDimensions.M p))
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) (t : Fin p.T) :=
  receptionInputAtRow (rows q) inputs t

@[simp] theorem receptionInputAtControl_ledger
    (control : ContinuousLearningRows.TimeControl p)
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) :
    (receptionInputAtControl control inputs).ledger = inputs.1 := rfl

@[simp] theorem receptionInputAtControl_upDecoderBank
    (control : ContinuousLearningRows.TimeControl p)
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) :
    (receptionInputAtControl control inputs).upDecoderBank = inputs.2.1 := rfl

@[simp] theorem receptionInputAtControl_slot
    (control : ContinuousLearningRows.TimeControl p)
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) :
    (receptionInputAtControl control inputs).slot = PublicDiscreteDraws.slotDraw control.1 := rfl

@[simp] theorem receptionInputAtControl_selectedFollower
    (control : ContinuousLearningRows.TimeControl p)
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) :
    (receptionInputAtControl control inputs).selectedFollower =
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1 := by
  exact selectedFollowerIndex_eq_draw control

@[simp] theorem receptionInputAtControl_affineSample
    (control : ContinuousLearningRows.TimeControl p)
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) :
    (receptionInputAtControl control inputs).affineSample =
      control.2 (1, selectedChannelFollower control) := rfl

@[simp] theorem receptionInputAtControl_time
    (control : ContinuousLearningRows.TimeControl p)
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) :
    (receptionInputAtControl control inputs).time = inputs.2.2.1 := rfl

@[simp] theorem receptionInputAtControl_ownObservation
    (control : ContinuousLearningRows.TimeControl p)
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) :
    (receptionInputAtControl control inputs).ownObservation = inputs.2.2.2 := rfl

theorem receptionInputAtControl_eq_of_same_control
    (control₁ control₂ : ContinuousLearningRows.TimeControl p)
    (inputs : ReceptionLocalInputs p eta heta hcap n hn)
    (hcontrol : control₁ = control₂) :
    receptionInputAtControl control₁ inputs = receptionInputAtControl control₂ inputs := by
  rw [hcontrol]

/-- The operation call is exactly the existing checked `receiveUp`; no
parallel decoder, acceptance check, or result carrier is introduced. -/
def receiveUpAtRow
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) (t : Fin p.T) :=
  CoordinatorUpReception.receiveUp (receptionInputAtRow row inputs t)

@[simp] theorem receiveUpAtRow_eq_receiveUp
    (row : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) (t : Fin p.T) :
    receiveUpAtRow row inputs t =
      CoordinatorUpReception.receiveUp (receptionInputAtRow row inputs t) := rfl

def receiveUpAtSelectedRow
    (rows : CompletePublicTable.CompleteRows p) (q : Fin (ConstructorDimensions.M p))
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) (t : Fin p.T) :=
  receiveUpAtRow (rows q) inputs t

theorem receiveUpAtRow_eq_of_same_current_control
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) (t : Fin p.T)
    (hcontrol : row₁.2 t = row₂.2 t) :
    receiveUpAtRow row₁ inputs t = receiveUpAtRow row₂ inputs t := by
  unfold receiveUpAtRow receptionInputAtRow
  rw [hcontrol]

theorem receiveUpAtSelectedRow_eq_of_same_current_control
    (rows₁ rows₂ : CompletePublicTable.CompleteRows p)
    (q : Fin (ConstructorDimensions.M p))
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) (t : Fin p.T)
    (hcontrol : (rows₁ q).2 t = (rows₂ q).2 t) :
    receiveUpAtSelectedRow rows₁ q inputs t = receiveUpAtSelectedRow rows₂ q inputs t := by
  exact receiveUpAtRow_eq_of_same_current_control (rows₁ q) (rows₂ q) inputs t hcontrol

theorem receiveUpAtSelectedRow_eq_of_same_selected_row
    (rows₁ rows₂ : CompletePublicTable.CompleteRows p)
    (q : Fin (ConstructorDimensions.M p))
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) (t : Fin p.T)
    (hrow : rows₁ q = rows₂ q) :
    receiveUpAtSelectedRow rows₁ q inputs t =
      receiveUpAtSelectedRow rows₂ q inputs t := by
  change receiveUpAtRow (rows₁ q) inputs t = receiveUpAtRow (rows₂ q) inputs t
  rw [hrow]

/-! ## Measurability from the full continuous control and inputs registers -/

private theorem measurable_selectedUpSampleControl :
    Measurable (fun control : ContinuousLearningRows.TimeControl p =>
      control.2 (1, selectedChannelFollower control)) := by
  classical
  let selected := fun control : ContinuousLearningRows.TimeControl p =>
    selectedChannelFollower control
  have hselected : Measurable selected := measurable_selectedChannelFollower.comp measurable_id
  have hfamily : Measurable (fun control : ContinuousLearningRows.TimeControl p => control.2) :=
    measurable_snd
  apply measurable_to_countable'
  intro sample
  have hfiber :
      {control : ContinuousLearningRows.TimeControl p |
          control.2 (1, selected control) = sample} =
        ⋃ i : Fin (ContinuousLearningRows.d p),
          {control | selected control = i} ∩
            {control | control.2 (1, i) = sample} := by
    ext control
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨selected control, rfl, h⟩
    · rintro ⟨i, hi, hs⟩
      rw [hi]
      exact hs
  change MeasurableSet {control : ContinuousLearningRows.TimeControl p |
    control.2 (1, selected control) = sample}
  rw [hfiber]
  exact MeasurableSet.iUnion fun i =>
    (measurableSet_eq_fun hselected measurable_const).inter
      (measurableSet_eq_fun ((measurable_pi_apply (1, i)).comp hfamily) measurable_const)

private theorem measurable_receptionInputAtControl :
    Measurable (fun x : ContinuousLearningRows.TimeControl p ×
        ReceptionLocalInputs p eta heta hcap n hn =>
      receptionInputAtControl x.1 x.2) := by
  classical
  let control := fun x : ContinuousLearningRows.TimeControl p ×
      ReceptionLocalInputs p eta heta hcap n hn => x.1
  let inputs := fun x : ContinuousLearningRows.TimeControl p ×
      ReceptionLocalInputs p eta heta hcap n hn => x.2
  have hslot : Measurable (fun x => PublicDiscreteDraws.slotDraw (control x).1) :=
    (PublicDiscreteDraws.measurable_slotDraw).comp (measurable_fst.comp measurable_fst)
  have hselected : Measurable (fun x =>
      selectedFollowerIndex (control x)) :=
    measurable_selectedFollowerIndex.comp measurable_fst
  have hsample : Measurable (fun x =>
      (control x).2 (1, selectedChannelFollower (control x))) :=
    measurable_selectedUpSampleControl.comp measurable_fst
  have hledger : Measurable (fun x => (inputs x).1) := measurable_fst.comp measurable_snd
  have hbank : Measurable (fun x => (inputs x).2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have htime : Measurable (fun x => (inputs x).2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hobservation : Measurable (fun x => (inputs x).2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  apply measurable_to_countable'
  intro target
  have hfiber :
      {x : ContinuousLearningRows.TimeControl p ×
          ReceptionLocalInputs p eta heta hcap n hn |
          receptionInputAtControl x.1 x.2 = target} =
        {x | (x.2).1 = target.ledger} ∩
        ({x | (x.2).2.1 = target.upDecoderBank} ∩
        ({x | (x.2).2.2.1 = target.time} ∩
        ({x | (x.2).2.2.2 = target.ownObservation} ∩
        ({x | PublicDiscreteDraws.slotDraw x.1.1 = target.slot} ∩
        ({x | selectedFollowerIndex x.1 = target.selectedFollower} ∩
         {x | x.1.2 (1, selectedChannelFollower x.1) = target.affineSample}))))) := by
    ext x
    change receptionInputAtControl x.1 x.2 = target ↔
      x.2.1 = target.ledger ∧
      x.2.2.1 = target.upDecoderBank ∧
      x.2.2.2.1 = target.time ∧
      x.2.2.2.2 = target.ownObservation ∧
      PublicDiscreteDraws.slotDraw x.1.1 = target.slot ∧
      selectedFollowerIndex x.1 = target.selectedFollower ∧
      x.1.2 (1, selectedChannelFollower x.1) = target.affineSample
    constructor
    · intro h
      cases h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨hledger, hbank, htime, hobservation, hslot, hselected, hsample⟩
      cases target with
      | mk ledger bank slot follower sample time observation =>
        change x.2.1 = ledger at hledger
        change x.2.2.1 = bank at hbank
        change x.2.2.2.1 = time at htime
        change x.2.2.2.2 = observation at hobservation
        change PublicDiscreteDraws.slotDraw x.1.1 = slot at hslot
        change selectedFollowerIndex x.1 = follower at hselected
        change x.1.2 (1, selectedChannelFollower x.1) = sample at hsample
        subst ledger
        subst bank
        subst slot
        subst follower
        subst sample
        subst time
        subst observation
        rfl
  change MeasurableSet {x : ContinuousLearningRows.TimeControl p ×
    ReceptionLocalInputs p eta heta hcap n hn |
    receptionInputAtControl x.1 x.2 = target}
  rw [hfiber]
  refine (measurableSet_eq_fun hledger measurable_const).inter ?_
  refine (measurableSet_eq_fun hbank measurable_const).inter ?_
  refine (measurableSet_eq_fun htime measurable_const).inter ?_
  refine (measurableSet_eq_fun hobservation measurable_const).inter ?_
  refine (measurableSet_eq_fun hslot measurable_const).inter ?_
  refine (measurableSet_eq_fun hselected measurable_const).inter ?_
  change MeasurableSet
    ((fun x : ContinuousLearningRows.TimeControl p ×
      ReceptionLocalInputs p eta heta hcap n hn =>
        x.1.2 (1, selectedChannelFollower x.1)) ⁻¹' {target.affineSample})
  exact hsample (measurableSet_singleton target.affineSample)

theorem measurable_receptionInputAtRow
    (t : Fin p.T) :
    Measurable (fun x : CompletePublicTable.CompleteRow p ×
        ReceptionLocalInputs p eta heta hcap n hn =>
      receptionInputAtRow x.1 x.2 t) := by
  have hcontrol : Measurable (fun x : CompletePublicTable.CompleteRow p ×
      ReceptionLocalInputs p eta heta hcap n hn => x.1.2 t) :=
    (ContinuousLearningRows.measurable_controlAt t).comp
      (measurable_snd.comp measurable_fst)
  exact measurable_receptionInputAtControl.comp (hcontrol.prodMk measurable_snd)

theorem measurable_receptionInputAtSelectedRow
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    Measurable (fun x : CompletePublicTable.CompleteRows p ×
        ReceptionLocalInputs p eta heta hcap n hn =>
      receptionInputAtSelectedRow x.1 q x.2 t) := by
  have hrow : Measurable (fun x : CompletePublicTable.CompleteRows p ×
      ReceptionLocalInputs p eta heta hcap n hn => x.1 q) :=
    (CompletePublicTable.measurable_completeRowProjection p q).comp measurable_fst
  exact (measurable_receptionInputAtRow (p := p) (eta := eta) (heta := heta)
    (hcap := hcap) (n := n) (hn := hn) t).comp (hrow.prodMk measurable_snd)

theorem measurable_receiveUpAtRow (t : Fin p.T) :
    Measurable (fun x : CompletePublicTable.CompleteRow p ×
        ReceptionLocalInputs p eta heta hcap n hn =>
      receiveUpAtRow x.1 x.2 t) := by
  have hinput := measurable_receptionInputAtRow (p := p) (eta := eta) (heta := heta)
    (hcap := hcap) (n := n) (hn := hn) t
  have hop : Measurable (fun input : CoordinatorUpReception.ReceptionInput
      p eta heta hcap n hn => CoordinatorUpReception.receiveUp input) :=
    Measurable.of_discrete
  exact hop.comp hinput

theorem measurable_receiveUpAtSelectedRow
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    Measurable (fun x : CompletePublicTable.CompleteRows p ×
        ReceptionLocalInputs p eta heta hcap n hn =>
      receiveUpAtSelectedRow x.1 q x.2 t) := by
  have hinput := measurable_receptionInputAtSelectedRow (p := p) (eta := eta) (heta := heta)
    (hcap := hcap) (n := n) (hn := hn) q t
  have hop : Measurable (fun input : CoordinatorUpReception.ReceptionInput
      p eta heta hcap n hn => CoordinatorUpReception.receiveUp input) :=
    Measurable.of_discrete
  exact hop.comp hinput

def rawDecoderOutputAtSelectedRow
    (rows : CompletePublicTable.CompleteRows p) (q : Fin (ConstructorDimensions.M p))
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) (t : Fin p.T) :=
  (CoordinatorUpReception.decoderTransition
    (receptionInputAtSelectedRow rows q inputs t)).2

def parsedDecoderOutputAtSelectedRow
    (rows : CompletePublicTable.CompleteRows p) (q : Fin (ConstructorDimensions.M p))
    (inputs : ReceptionLocalInputs p eta heta hcap n hn) (t : Fin p.T) :=
  CoordinatorUpReception.parseDecoderOutput (p := p) (eta := eta)
    (rawDecoderOutputAtSelectedRow rows q inputs t)

theorem measurable_rawDecoderOutputAtSelectedRow
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    Measurable (fun x : CompletePublicTable.CompleteRows p ×
        ReceptionLocalInputs p eta heta hcap n hn =>
      rawDecoderOutputAtSelectedRow x.1 q x.2 t) := by
  have hinput := measurable_receptionInputAtSelectedRow (p := p) (eta := eta) (heta := heta)
    (hcap := hcap) (n := n) (hn := hn) q t
  have hraw : Measurable (fun input : CoordinatorUpReception.ReceptionInput
      p eta heta hcap n hn =>
      (CoordinatorUpReception.decoderTransition input).2) := Measurable.of_discrete
  exact hraw.comp hinput

theorem measurable_parsedDecoderOutputAtSelectedRow
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    Measurable (fun x : CompletePublicTable.CompleteRows p ×
        ReceptionLocalInputs p eta heta hcap n hn =>
      parsedDecoderOutputAtSelectedRow x.1 q x.2 t) := by
  have hraw := measurable_rawDecoderOutputAtSelectedRow (p := p) (eta := eta) (heta := heta)
    (hcap := hcap) (n := n) (hn := hn) q t
  have hparse : Measurable (CoordinatorUpReception.parseDecoderOutput
      (p := p) (eta := eta)) := Measurable.of_discrete
  exact hparse.comp hraw

end Bandits.Support.CoordinatorUpMeasurability

end
