/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCollectionPreEffectUpCredit

import Lean.Elab.Tactic.Omega

/-!
# Complete collection filtered-UP replay and candidate domains

Sources: `sources/zip4/manuscript/06_interruptions.tex:64-100,164-177,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-64`.

This conditional internal producer uses the literal checked START, effective
filtered UP parse, and local acceptance equations at one actual complete-suffix
round. It proves the concrete all-calendar replay and checked decode candidate
domains before any receiver result. It does not produce the recorder or START,
assert true-message coupling, or close the physical source branch.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteCollectionUpDecodeDomains

open ConstructorDimensions
open ReferenceActivePhysicalStep
open CoordinatorCollectionLedger
open ReferenceCollectionSegmentExtraction
open ReferenceCollectionPhaseHistory

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)
variable (source : BootstrapPrivateRoundStreams.SourceInput p)

local notation "R" => ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate source rewards C_star C_h

private theorem allFin_eq_true_iff {length : ℕ} (test : Fin length → Bool) :
    allFin length test = true ↔ ∀ i, test i = true := by
  unfold allFin
  rw [List.all_eq_true]
  constructor
  · intro hall i
    exact hall (test i) (by simp)
  · intro hall value hvalue
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hvalue
    subst value
    exact hall i

private theorem replayRecords?_eq_some_map
    (l : Ledger rate) (a : Fin p.K) (indices : List (Fin p.T))
    (enabled : Fin p.T → Bool)
    (henabled : ∀ r ∈ indices, l.enabledHistory r = some (enabled r)) :
    replayRecords? l a indices = some (indices.map fun r =>
      (enabled r && decide (sourceRound r < l.freezeAt), bufferedArrival l a r)) := by
  induction indices with
  | nil => rfl
  | cons r rest ih =>
      have hr := henabled r (by simp)
      have hrest : ∀ s ∈ rest, l.enabledHistory s = some (enabled s) := by
        intro s hs
        exact henabled s (by simp [hs])
      simp [replayRecords?, hr, ih hrest, sourceRound]

private theorem transition_mass_le (capacity score backlog arrival : ℕ)
    (flag : Bool) :
    (QueueReplay.transition capacity (score, backlog) (flag, arrival)).1 +
        (QueueReplay.transition capacity (score, backlog) (flag, arrival)).2 ≤
      score + backlog + arrival := by
  cases flag with
  | false => simp [QueueReplay.transition]
  | true =>
      change (score + min capacity (backlog + arrival)) +
          (backlog + arrival - min capacity (backlog + arrival)) ≤
        score + backlog + arrival
      have hservice : min capacity (backlog + arrival) ≤ backlog + arrival :=
        Nat.min_le_right _ _
      have hcancel := Nat.sub_add_cancel hservice
      omega

private theorem replay_mass_bound (capacity initialScore initialBacklog D : ℕ)
    (records : List (Bool × ℕ))
    (harrival : ∀ record ∈ records, record.2 ≤ D) :
    let endpoint := QueueReplay.replay capacity (initialScore, initialBacklog) records
    endpoint.1 + endpoint.2 ≤ initialScore + initialBacklog + records.length * D := by
  induction records generalizing initialScore initialBacklog with
  | nil => simp [QueueReplay.replay]
  | cons record rest ih =>
      have hhead := harrival record (by simp)
      have htail : ∀ next ∈ rest, next.2 ≤ D := by
        intro next hnext
        exact harrival next (by simp [hnext])
      let advanced := QueueReplay.transition capacity
        (initialScore, initialBacklog) record
      have hstep : advanced.1 + advanced.2 ≤
          initialScore + initialBacklog + record.2 := by
        cases record with
        | mk flag arrival =>
            simpa [advanced] using transition_mass_le capacity
              initialScore initialBacklog arrival flag
      have hrest := ih advanced.1 advanced.2 htail
      change (QueueReplay.replay capacity advanced rest).1 +
          (QueueReplay.replay capacity advanced rest).2 ≤ _
      calc
        _ ≤ advanced.1 + advanced.2 + rest.length * D := hrest
        _ ≤ initialScore + initialBacklog + record.2 + rest.length * D :=
          Nat.add_le_add_right hstep _
        _ ≤ initialScore + initialBacklog + D + rest.length * D := by omega
        _ = initialScore + initialBacklog + (rest.length + 1) * D := by
          rw [Nat.add_mul]
          simp
          omega

private theorem replay_prefix_last_service_le (capacity initialQueue : ℕ)
    (records : List (Bool × ℕ)) :
    ∀ h, h ≤ records.length → 0 < h →
      let endpoint := QueueReplay.replay capacity (0, initialQueue) (records.take h)
      let previous := QueueReplay.replay capacity (0, initialQueue)
        (records.take (h - 1))
      endpoint.1 - previous.1 ≤ capacity := by
  intro h hbound hpositive
  have hprevlt : h - 1 < records.length := by omega
  have htake := List.take_succ_drop (l := records) (n := h - 1) (stop := 0)
    (by simpa using hprevlt)
  simp only [List.drop_zero, Nat.zero_add] at htake
  have hsucc : (h - 1) + 1 = h := by omega
  rw [← hsucc, htake, QueueReplay.replay_append]
  let previous := QueueReplay.replay capacity (0, initialQueue)
    (records.take (h - 1))
  have hstep := ReplayWeightStability.transition_score_envelope capacity
    previous.1 previous.2 records[h - 1]
  change (QueueReplay.transition capacity (previous.1, previous.2)
    records[h - 1]).1 - previous.1 ≤ capacity
  omega

private theorem calendarIndices_source_at (start length : ℕ)
    (hbound : start + length ≤ p.T) (j : Fin length) :
    sourceRound ((calendarIndices p.T start length hbound).get
      ⟨j.val, by simp [calendarIndices]⟩) = start + j.val + 1 := by
  simp [calendarIndices, sourceRound]

private theorem calendarIndices_source_bounds (start length : ℕ)
    (hbound : start + length ≤ p.T) (r : Fin p.T)
    (hr : r ∈ calendarIndices p.T start length hbound) :
    start + 1 ≤ sourceRound r ∧ sourceRound r ≤ start + length := by
  have hr' : r ∈ List.ofFn (fun j : Fin length =>
      (⟨start + j.val, by have hj := j.isLt; omega⟩ : Fin p.T)) := by
    simpa [calendarIndices] using hr
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hr'
  have hval : r.val = start + j.val := by
    have hv := congrArg Fin.val hj
    simpa using hv.symm
  constructor
  · change start + 1 ≤ r.val + 1
    rw [hval]
    omega
  · change r.val + 1 ≤ start + length
    rw [hval]
    omega

private theorem armPendingCheck_eq_true_iff
    (l : Ledger rate) (a : Fin p.K) :
    armPendingCheck l a = true ↔ armPending l a := by
  unfold armPendingCheck anyFin
  rw [List.any_eq_true]
  simp [armPending]

private theorem allFin_option_isNone_eq_pendingCheck
    (l : Ledger rate) {α : Type*} (registers : Fin p.K → Option α)
    (hregisters : ∀ a, registers a = none ↔ armPending l a) :
    allFin p.K (fun a =>
      (registers a).isNone == armPendingCheck l a) = true := by
  apply (allFin_eq_true_iff _).2
  intro a
  by_cases hp : armPending l a
  · have hnone : registers a = none := (hregisters a).2 hp
    have hcheck : armPendingCheck l a = true :=
      (armPendingCheck_eq_true_iff rate l a).2 hp
    simp [hnone, hcheck]
  · have hnotNone : registers a ≠ none := by
      intro hnone
      exact hp ((hregisters a).1 hnone)
    have hcheck : armPendingCheck l a = false := by
      cases h : armPendingCheck l a with
      | false => rfl
      | true => exact False.elim (hp ((armPendingCheck_eq_true_iff rate l a).1 h))
    cases hreg : registers a with
    | none => exact False.elim (hnotNone hreg)
    | some value => simp [hcheck]

private theorem allFin_pending_field_zero
    (l : Ledger rate) (field : Fin p.K → ℕ)
    (hzero : ∀ a, armPending l a → field a = 0) :
    allFin p.K (fun a =>
      (!armPendingCheck l a) || decide (field a = 0)) = true := by
  apply (allFin_eq_true_iff _).2
  intro a
  by_cases hp : armPending l a
  · have hcheck : armPendingCheck l a = true :=
      (armPendingCheck_eq_true_iff rate l a).2 hp
    simp [hcheck, hzero a hp]
  · have hcheck : armPendingCheck l a = false := by
      cases h : armPendingCheck l a with
      | false => rfl
      | true => exact False.elim (hp ((armPendingCheck_eq_true_iff rate l a).1 h))
    simp [hcheck]

private theorem start_success_valid
    (l started : Ledger rate) (t : ℕ) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ))
    (hstart : startRound l t enabled raw = .success started) :
    validLedgerCheck started = true ∧ started.phase = Phase.started ∧
      started.cursor = t := by
  have hvalid : validLedgerCheck started = true := by
    unfold startRound at hstart
    by_cases hcond : validLedgerCheck l = true ∧ l.phase = Phase.ready ∧
        t = l.cursor ∧ 1 ≤ t ∧ t ≤ p.T ∧ rawInputDomainCheck raw = true
    · rcases hcond with ⟨hlvalid, hlphase, htime, hlow, hhigh, hraw⟩
      rw [htime] at hstart
      let idx : Fin p.T := ⟨l.cursor - 1, by omega⟩
      by_cases hslot : rawSlotFreshCheck l idx raw = true
      · let candidate := startRoundCandidate l idx enabled raw
        by_cases hcand : validLedgerCheck candidate = true
        · have heq : startRound l l.cursor enabled raw = .success candidate := by
            simp [startRound, hlvalid, hlphase, hraw, hslot, hcand,
              show 1 ≤ l.cursor by omega, show l.cursor ≤ p.T by omega,
              idx, candidate]
          have hresult : candidate = started := Checked.success.inj (heq.symm.trans hstart)
          rw [← hresult]
          exact hcand
        · simp [hlvalid, hlphase, hraw, hslot, hcand,
            show 1 ≤ l.cursor by omega, show l.cursor ≤ p.T by omega,
            idx, candidate] at hstart
      · simp [hlvalid, hlphase, hraw, hslot,
          show 1 ≤ l.cursor by omega, show l.cursor ≤ p.T by omega,
          idx] at hstart
    · simp [hcond] at hstart
  have hcand := CollectionCheckedExecution.startRound_success_candidate
    l started t enabled raw hstart
  have hphase : started.phase = Phase.started := by
    rw [hcand]
    simp [startRoundCandidate]
  have hcursor := CollectionCheckedExecution.startRound_success_cursor
    l started t enabled raw hstart
  exact ⟨hvalid, hphase, hcursor⟩

/-- The actual filtered-UP branch supplies canonical all-calendar replay
records, literal indices domains, and the validity test of the concrete decoded
candidate. The only conditional inputs are the local branch equations stated
below; recorder production, source-truth coupling, and receiver success remain
outside this result. -/
theorem complete_filtered_up_decode_domains
    (k : Fin (R).length)
    (c : Choice rate)
    (hchoice : choice (R[k.val]'k.isLt).input = some c)
    (o : CoordinatorRecordingOperation.Output p)
    (s : ReferenceActivePhysicalStep.Ledger rate)
    (hstart : startRound c.preLedger
      ((R[k.val]'k.isLt).input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger
        (R[k.val]'k.isLt).input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success s)
    (U : UpRecord p rate)
    (hparse : effectiveParse (R[k.val]'k.isLt).input s = some U)
    (hlocal : acceptUpCheck s
      (ReferenceActivePhysicalStep.upSenderIndex (R[k.val]'k.isLt).input) U = true) :
    let x := (R[k.val]'k.isLt).input
    let i := ReferenceActivePhysicalStep.upSenderIndex x
    let a := s.assignment.arm i
    ∃ (hs : (s.cutoff - 1) + (s.cursor - s.cutoff) ≤ p.T)
      (hc : s.cursor - 1 < p.T),
      ∃ past : List (Bool × ℕ), ∃ current : Bool × ℕ,
      let indices := calendarIndices p.T (s.cutoff - 1) (s.cursor - s.cutoff) hs
      let last : Fin p.T := ⟨s.cursor - 1, hc⟩
      replayRecords? s a indices = some past ∧
      replayRecords? s a [last] = some [current] ∧
      (past ++ [current]).length = s.cursor - s.cutoff + 1 ∧
      replayOutputDomainsCheck (p := p) (4 * rate.n) U.val.q
        (past ++ [current]) = true ∧
      validLedgerCheck (acceptUpCandidate s i U past current) = true ∧
      (∀ h, h ≤ (past ++ [current]).length →
        (QueueReplay.replay (4 * rate.n) (0, U.val.q)
          ((past ++ [current]).take h)).1 +
        (QueueReplay.replay (4 * rate.n) (0, U.val.q)
          ((past ++ [current]).take h)).2 ≤
          U.val.q + h * D p ∧
        U.val.q + h * D p ≤ p.T * D p) ∧
      (QueueReplay.replay (4 * rate.n) (0, U.val.q)
        (past ++ [current])).1 -
      (QueueReplay.replay (4 * rate.n) (0, U.val.q)
        ((past ++ [current]).take ((past ++ [current]).length - 1))).1 ≤
        4 * rate.n ∧ 4 * rate.n ≤ D p := by
  classical
  let x := (R[k.val]'k.isLt).input
  let i := ReferenceActivePhysicalStep.upSenderIndex x
  let a := s.assignment.arm i
  let t := x.time.val + 1
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o
  have hstart' : startRound c.preLedger t
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time) raw = .success s := by
    simpa [x, t, raw] using hstart
  have htag := start_success_valid rate c.preLedger s t
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time) raw hstart'
  have hcand := CollectionCheckedExecution.startRound_success_candidate
    c.preLedger s t (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time) raw hstart'
  have hcursor : s.cursor = t := htag.2.2
  have hphase : s.phase = Phase.started := htag.2.1
  have hvalid : validLedgerCheck s = true := htag.1
  have hcursorT : s.cursor ≤ p.T := by
    have htime : x.time.val < p.T := x.time.isLt
    rw [hcursor]
    dsimp [t]
    omega
  have hvalidParts := hvalid
  simp [validLedgerCheck, hphase, Bool.and_eq_true] at hvalidParts
  rcases hvalidParts with ⟨hparts, hrawDomains⟩
  rcases hparts with ⟨hparts, hregisterDomains⟩
  rcases hparts with ⟨hparts, hincrementPending⟩
  rcases hparts with ⟨hparts, hgammaPending⟩
  rcases hparts with ⟨hparts, hcutoffPending⟩
  rcases hparts with ⟨hparts, hcurrentPending⟩
  rcases hparts with ⟨hscalars, hhistory⟩
  rcases hscalars with ⟨hscalars, hcursorLeT⟩
  rcases hscalars with ⟨hscalars, hcursorLeTPlus⟩
  rcases hscalars with ⟨hscalars, hcutCursorCheck⟩
  rcases hscalars with ⟨hscalars, hfreezeTCheck⟩
  rcases hscalars with ⟨hscalars, hcutTCheck⟩
  rcases hscalars with ⟨hscalars, hcutFreezeCheck⟩
  rcases hscalars with ⟨hscalars, hcutPosCheck⟩
  rcases hscalars with ⟨hsigmaPosCheck, hsigmaTCheck⟩
  have hcutPos : 1 ≤ s.cutoff := hcutPosCheck
  have hcutCursor : s.cutoff ≤ s.cursor := hcutCursorCheck
  have hcursorLeT' : s.cursor ≤ p.T := hcursorLeT
  have hcutoffLeT : s.cutoff ≤ p.T := hcutTCheck
  have hindexBound : (s.cutoff - 1) + (s.cursor - s.cutoff) ≤ p.T := by omega
  have hcurrentBound : s.cursor - 1 < p.T := by omega
  let hs : (s.cutoff - 1) + (s.cursor - s.cutoff) ≤ p.T := hindexBound
  let hc : s.cursor - 1 < p.T := hcurrentBound
  let indices := calendarIndices p.T (s.cutoff - 1) (s.cursor - s.cutoff) hs
  let last : Fin p.T := ⟨s.cursor - 1, hc⟩
  have hEnabled : ∀ r ∈ indices, (s.enabledHistory r).isSome = true := by
    intro r hr
    have hrange := calendarIndices_source_bounds (s.cutoff - 1)
      (s.cursor - s.cutoff) hs r (by simpa [indices] using hr)
    have hrange' : s.cutoff ≤ sourceRound r ∧ sourceRound r ≤ s.cursor := by
      constructor <;> omega
    have hentry := (allFin_eq_true_iff _).1 hhistory r
    have hcondition : s.cutoff ≤ sourceRound r := hrange'.1
    have hupper : sourceRound r ≤ s.cursor := hrange'.2
    have heq : (s.enabledHistory r).isSome = decide (sourceRound r ≤ s.cursor) := by
      have h := hentry
      have hbefore : ¬ sourceRound r < s.cutoff := by omega
      simp [hbefore] at h
      exact h
    simpa [hupper] using heq
  have hCurrentEnabled : (s.enabledHistory last).isSome = true := by
    have hall := (allFin_eq_true_iff _).1 hhistory last
    have hround : sourceRound last = s.cursor := by
      simp [last, sourceRound]
      omega
    have hcondition : s.cutoff ≤ sourceRound last := by rw [hround]; exact hcutCursor
    have heq : (s.enabledHistory last).isSome = decide (sourceRound last ≤ s.cursor) := by
      have hbefore : ¬ sourceRound last < s.cutoff := by omega
      simp [hbefore] at hall
      exact hall
    simpa [hround] using heq
  have hEnabledSome : ∀ r ∈ indices, ∃ b, s.enabledHistory r = some b := by
    intro r hr
    have h := hEnabled r hr
    cases he : s.enabledHistory r with
    | none => simp [he] at h
    | some b => exact ⟨b, rfl⟩
  let past : List (Bool × ℕ) := indices.map fun r =>
    ((s.enabledHistory r).getD false && decide (sourceRound r < s.freezeAt),
      bufferedArrival s a r)
  have hPast : replayRecords? s a indices = some past := by
    apply replayRecords?_eq_some_map rate s a indices (fun r => (s.enabledHistory r).getD false)
    intro r hr
    obtain ⟨b, hb⟩ := hEnabledSome r hr
    simp [hb]
  let current : Bool × ℕ :=
    ((s.enabledHistory last).getD false && decide (sourceRound last < s.freezeAt),
      bufferedArrival s a last)
  have hCurrent : replayRecords? s a [last] = some [current] := by
    apply replayRecords?_eq_some_map rate s a [last] (fun r => (s.enabledHistory r).getD false)
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    have hflagExists : ∃ b, s.enabledHistory last = some b := by
      cases hflag : s.enabledHistory last with
      | none => simp [hflag] at hCurrentEnabled
        | some b => exact ⟨b, rfl⟩
    obtain ⟨b, hb⟩ := hflagExists
    simp [hb]
  have hprefixLength : indices.length = s.cursor - s.cutoff := by
    simp [indices, calendarIndices_length]
  have hpastLength : past.length = s.cursor - s.cutoff := by
    simp [past, hprefixLength]
  have hrecordsLength : (past ++ [current]).length = s.cursor - s.cutoff + 1 := by
    simp [hpastLength]
  have hrawPoint : ∀ b r amount, s.rawBuffer b r = some amount →
      0 < amount ∧ amount ≤ D p ∧ s.cutoff ≤ sourceRound r ∧
        sourceRound r < s.freezeAt ∧ sourceRound r ≤ s.cursor ∧ armPendingCheck s b = true := by
    intro b r amount hcell
    have hrawExpanded := hrawDomains
    simp only [rawEntryDomainsCheck] at hrawExpanded
    have hall := (allFin_eq_true_iff _).1 hrawExpanded b
    have hall' := (allFin_eq_true_iff _).1 hall r
    simp only [hcell] at hall'
    simp [hphase, Bool.and_eq_true, decide_eq_true_eq] at hall'
    rcases hall' with ⟨⟨⟨⟨⟨hpos, hD⟩, hcut⟩, hfreeze⟩, htime⟩, hpending⟩
    exact ⟨hpos, hD, hcut, hfreeze, htime, hpending⟩
  have harrivalBound : ∀ r ∈ indices, bufferedArrival s a r ≤ D p := by
    intro r hr
    cases hcell : s.rawBuffer a r with
    | none => simp [bufferedArrival, hcell]
    | some amount =>
        have hdom := hrawPoint a r amount hcell
        simpa [bufferedArrival, hcell] using hdom.2.1
  have hcurrentArrival : bufferedArrival s a last ≤ D p := by
    cases hcell : s.rawBuffer a last with
    | none => simp [bufferedArrival, hcell]
    | some amount =>
        have hdom := hrawPoint a last amount hcell
        simpa [bufferedArrival, hcell] using hdom.2.1
  have hrecordsArrival : ∀ record ∈ past ++ [current], record.2 ≤ D p := by
    intro record hmem
    rcases List.mem_append.mp hmem with hpastMem | hcurrentMem
    · obtain ⟨r, hr, hrecord⟩ := List.mem_map.mp hpastMem
      have hsnd := congrArg Prod.snd hrecord
      rw [← hsnd]
      exact harrivalBound r hr
    · simp only [List.mem_singleton] at hcurrentMem
      subst record
      exact hcurrentArrival
  have hcreditDelta := ReferenceCompleteCollectionPreEffectUpCredit.complete_filtered_up_pre_effect_credit
    rate rewards C_star C_h source k c hchoice o s hstart U hparse hlocal
  obtain ⟨hcredit0, hdelta⟩ := hcreditDelta
  have hstartBase : s.baseScore = c.preLedger.baseScore := by
    rw [hcand]
    rfl
  have hstartCutoff : s.cutoff = c.preLedger.cutoff := by
    rw [hcand]
    rfl
  have hcredit : s.baseScore i + U.val.S + U.val.q ≤ (s.cutoff - 1) * D p := by
    rw [hstartBase, hstartCutoff]
    exact hcredit0
  have hregBool : registerDomainsCheck s = true := hregisterDomains
  have hregParts := hregBool
  simp only [registerDomainsCheck, Bool.and_eq_true] at hregParts
  rcases hregParts with ⟨hregParts, hgammaOld⟩
  rcases hregParts with ⟨hregParts, hincrementOld⟩
  rcases hregParts with ⟨hregParts, hbaseOld⟩
  rcases hregParts with ⟨hcurrentOld, hcutoffOld⟩
  have hbaseAll := (allFin_eq_true_iff _).1 hbaseOld
  have hbaseBound : s.baseScore i ≤ p.T * D p := of_decide_eq_true (hbaseAll i)
  have hqBound : U.val.q ≤ p.T * D p := by
    have hcutMinus : s.cutoff - 1 ≤ p.T := by omega
    have hmul := Nat.mul_le_mul_right (D p) hcutMinus
    omega
  have hscoreBound : s.baseScore i + U.val.S ≤ p.T * D p := by
    have hcredit' : s.baseScore i + U.val.S ≤ (s.cutoff - 1) * D p := by omega
    have hcutT : s.cutoff - 1 ≤ p.T := by omega
    exact (hcredit'.trans (Nat.mul_le_mul_right (D p) hcutT))
  have hfourN : 4 * rate.n ≤ D p := ActiveFollowerDownAcceptance.four_n_le_D p rate
  let records := past ++ [current]
  have hprefixMass : ∀ h, h ≤ records.length →
      (QueueReplay.replay (4 * rate.n) (0, U.val.q) (records.take h)).1 +
        (QueueReplay.replay (4 * rate.n) (0, U.val.q) (records.take h)).2 ≤
          U.val.q + h * D p := by
    intro h hh
    have htakeArrivals : ∀ record ∈ records.take h, record.2 ≤ D p := by
      intro record hmem
      apply hrecordsArrival record
      exact List.mem_of_mem_take hmem
    have hmass := replay_mass_bound (4 * rate.n) 0 U.val.q (D p)
      (records.take h) htakeArrivals
    have hlen : (records.take h).length ≤ h := by simp
    have hlenMul := Nat.mul_le_mul_right (D p) hlen
    have hbound := hmass
    calc
      _ = (QueueReplay.replay (4 * rate.n) (0, U.val.q)
        (records.take h)).1 +
        (QueueReplay.replay (4 * rate.n) (0, U.val.q)
          (records.take h)).2 := rfl
      _ ≤ U.val.q + (records.take h).length * D p := by
        simpa [Nat.zero_add] using hmass
      _ ≤ U.val.q + h * D p := Nat.add_le_add_left hlenMul _
  have hprefixTime : ∀ h, h ≤ records.length → s.cutoff - 1 + h ≤ p.T := by
    intro h hh
    rw [hrecordsLength] at hh
    have hvT : s.cursor ≤ p.T := hcursorT
    omega
  have hprefixBound : ∀ h, h ≤ records.length →
      U.val.q + h * D p ≤ p.T * D p := by
    intro h hh
    have htime := hprefixTime h hh
    have hmul := Nat.mul_le_mul_right (D p) htime
    have hcreditQ : U.val.q ≤ (s.cutoff - 1) * D p := by
      calc
        U.val.q ≤ s.baseScore i + U.val.S + U.val.q := by omega
        _ ≤ (s.cutoff - 1) * D p := hcredit
    calc
      _ ≤ (s.cutoff - 1) * D p + h * D p := Nat.add_le_add_right hcreditQ _
      _ = (s.cutoff - 1 + h) * D p := by rw [Nat.add_mul]
      _ ≤ p.T * D p := hmul
  have hprefixService : ∀ h, h ≤ records.length → 0 < h →
      (QueueReplay.replay (4 * rate.n) (0, U.val.q) (records.take h)).1 -
        (QueueReplay.replay (4 * rate.n) (0, U.val.q)
          (records.take (h - 1))).1 ≤ 4 * rate.n :=
    replay_prefix_last_service_le (4 * rate.n) U.val.q records
  have hprefixDomains : ∀ q : Fin (records.length + 1),
      replayPrefixOutputDomainsCheck (p := p) (4 * rate.n) U.val.q records q = true := by
    intro q
    have hh : q.val ≤ records.length := by omega
    have hmass := hprefixMass q.val hh
    have hbound := hprefixBound q.val hh
    have hscore : (QueueReplay.replay (4 * rate.n) (0, U.val.q)
        (records.take q.val)).1 ≤ p.T * D p := by omega
    have hqueue : (QueueReplay.replay (4 * rate.n) (0, U.val.q)
        (records.take q.val)).2 ≤ p.T * D p := by omega
    by_cases hz : q.val = 0
    · have hzeroScore : 0 ≤ p.T * D p := by omega
      rw [hz] at hqueue
      have hzeroQueue : U.val.q ≤ p.T * D p := by
        simpa [QueueReplay.replay] using hqueue
      simp [replayPrefixOutputDomainsCheck, hz, QueueReplay.replay,
        hzeroScore, hzeroQueue]
    · have hservice := hprefixService q.val hh (by omega)
      have hserviceD := hservice.trans hfourN
      simp [replayPrefixOutputDomainsCheck, hz, hscore, hqueue, hserviceD]
  have hprefixAll : allFin (records.length + 1)
      (fun q => replayPrefixOutputDomainsCheck (p := p) (4 * rate.n)
        U.val.q records q) = true :=
    (allFin_eq_true_iff _).2 hprefixDomains
  have harrivalAll : records.all (fun record => decide (record.2 ≤ D p)) = true := by
    apply List.all_eq_true.mpr
    intro record hm
    exact decide_eq_true (hrecordsArrival record hm)
  have hrecordsLe : records.length ≤ p.T := by
    calc
      records.length = s.cursor - s.cutoff + 1 := hrecordsLength
      _ ≤ s.cursor := by omega
      _ ≤ p.T := hcursorT
  have hout : replayOutputDomainsCheck (p := p) (4 * rate.n) U.val.q records = true := by
    simp [replayOutputDomainsCheck, hrecordsLe, harrivalAll, hprefixAll]
  have hrecordsRefl : records.length ≤ records.length := Nat.le_refl _
  have hrecordsPos : 0 < records.length := by
    rw [hrecordsLength]
    omega
  have hfinalService := hprefixService records.length hrecordsRefl hrecordsPos
  have hfinalServiceFull :
      (QueueReplay.replay (4 * rate.n) (0, U.val.q) records).1 -
        (QueueReplay.replay (4 * rate.n) (0, U.val.q)
          (records.take (records.length - 1))).1 ≤ 4 * rate.n := by
    simpa only [List.take_length] using hfinalService
  have hfullMass :
      (QueueReplay.replay (4 * rate.n) (0, U.val.q) records).1 +
        (QueueReplay.replay (4 * rate.n) (0, U.val.q) records).2 ≤
          U.val.q + records.length * D p := by
    simpa only [List.take_length] using hprefixMass records.length (by omega)
  have hfullBound : U.val.q + records.length * D p ≤ p.T * D p :=
    hprefixBound records.length (by omega)
  have hrecordsPrevious : records.take (records.length - 1) = past := by
    simp [records, hpastLength]
  have hfields := acceptUpCandidate_recovered_fields s i U past current
  let candidate := acceptUpCandidate s i U past current
  have hcurrentRecovered : candidate.currentRegisters a =
      some ⟨(QueueReplay.replay (4 * rate.n) (0, U.val.q) records).2,
        (QueueReplay.replay (4 * rate.n) (0, U.val.q) records).1 -
          (QueueReplay.replay (4 * rate.n) (0, U.val.q)
            (records.take (records.length - 1))).1⟩ := by
    simpa [candidate, a, records, hrecordsPrevious] using hfields.1
  have hincrementRecovered : candidate.increment a =
      (QueueReplay.replay (4 * rate.n) (0, U.val.q) records).1 := by
    simpa [candidate, a, records] using hfields.2.1
  have hcutoffRecovered : candidate.cutoffRegisters a =
      some ⟨s.baseScore i + U.val.S, U.val.q, U.val.delta⟩ := by
    simpa [candidate, a] using hfields.2.2
  have hlocalParts := hlocal
  simp only [acceptUpCheck, Bool.and_eq_true, decide_eq_true_eq] at hlocalParts
  have hpendingInput : i ∈ s.pending := hlocalParts.2.1
  have hpendingA : armPending s a := ⟨i, hpendingInput, rfl⟩
  have hregistersInput : ∀ b,
      (s.currentRegisters b = none ↔ armPending s b) ∧
      (s.cutoffRegisters b = none ↔ armPending s b) := by
    intro b
    have hcurBool := (allFin_eq_true_iff _).1 hcurrentPending b
    have hcutBool := (allFin_eq_true_iff _).1 hcutoffPending b
    have hcurRel : (s.currentRegisters b).isNone = armPendingCheck s b := by
      simpa only [beq_iff_eq] using hcurBool
    have hcutRel : (s.cutoffRegisters b).isNone = armPendingCheck s b := by
      simpa only [beq_iff_eq] using hcutBool
    constructor
    · constructor
      · intro hnone
        have hbool : (s.currentRegisters b).isNone = true := by simp [hnone]
        have hcheck : armPendingCheck s b = true := hcurRel.symm.trans hbool
        exact (armPendingCheck_eq_true_iff rate s b).1 hcheck
      · intro hp
        have hcheck := (armPendingCheck_eq_true_iff rate s b).2 hp
        have hbool : (s.currentRegisters b).isNone = true := hcurRel.trans hcheck
        cases hcur : s.currentRegisters b with
        | none => rfl
        | some value => simp [hcur] at hbool
    · constructor
      · intro hnone
        have hbool : (s.cutoffRegisters b).isNone = true := by simp [hnone]
        have hcheck : armPendingCheck s b = true := hcutRel.symm.trans hbool
        exact (armPendingCheck_eq_true_iff rate s b).1 hcheck
      · intro hp
        have hcheck := (armPendingCheck_eq_true_iff rate s b).2 hp
        have hbool : (s.cutoffRegisters b).isNone = true := hcutRel.trans hcheck
        cases hcut : s.cutoffRegisters b with
        | none => rfl
        | some value => simp [hcut] at hbool
  have hArmAfter : ∀ b,
      armPending candidate b ↔ b ≠ a ∧ armPending s b := by
    intro b
    change (∃ j, j ∈ s.pending.erase i ∧ s.assignment.arm j = b) ↔ _
    constructor
    · rintro ⟨j, hj, hjarm⟩
      rcases Finset.mem_erase.mp hj with ⟨hji, hjpending⟩
      have hbne : b ≠ a := by
        intro hba
        apply hji
        apply s.assignment.injective
        calc
          s.assignment.arm j = b := hjarm
          _ = a := hba
          _ = s.assignment.arm i := rfl
      exact ⟨hbne, ⟨j, hjpending, hjarm⟩⟩
    · rintro ⟨hbne, ⟨j, hjpending, hjarm⟩⟩
      have hji : j ≠ i := by
        intro hji
        subst j
        apply hbne
        simpa [a] using hjarm.symm
      exact ⟨j, Finset.mem_erase.mpr ⟨hji, hjpending⟩, hjarm⟩
  have hregistersAfter : ∀ b,
      (candidate.currentRegisters b = none ↔ armPending candidate b) ∧
      (candidate.cutoffRegisters b = none ↔ armPending candidate b) := by
    intro b
    by_cases hba : b = a
    · subst b
      have hnotPending : ¬ armPending candidate a := by
        intro hp
        exact (hArmAfter a).mp hp |>.1 rfl
      constructor
      · constructor
        · intro hnone
          rw [hcurrentRecovered] at hnone
          cases hnone
        · intro hp
          exact False.elim (hnotPending hp)
      · constructor
        · intro hnone
          rw [hcutoffRecovered] at hnone
          cases hnone
        · intro hp
          exact False.elim (hnotPending hp)
    · have hcurrentFrame : candidate.currentRegisters b = s.currentRegisters b := by
        simp [candidate, acceptUpCandidate, a, hba]
      have hcutoffFrame : candidate.cutoffRegisters b = s.cutoffRegisters b := by
        simp [candidate, acceptUpCandidate, a, hba]
      have hpendingFrame : armPending candidate b ↔ armPending s b := by
        rw [hArmAfter b]
        simp [hba]
      rw [hcurrentFrame, hcutoffFrame, hpendingFrame]
      exact hregistersInput b
  have hcurrentPendingAfter : allFin p.K (fun b =>
      (candidate.currentRegisters b).isNone == armPendingCheck candidate b) = true :=
    allFin_option_isNone_eq_pendingCheck rate candidate candidate.currentRegisters
      (fun b => (hregistersAfter b).1)
  have hcutoffPendingAfter : allFin p.K (fun b =>
      (candidate.cutoffRegisters b).isNone == armPendingCheck candidate b) = true :=
    allFin_option_isNone_eq_pendingCheck rate candidate candidate.cutoffRegisters
      (fun b => (hregistersAfter b).2)
  have hgammaPendingAfter : allFin p.K (fun b =>
      (!armPendingCheck candidate b) || decide (candidate.gammaLoc b = 0)) = true :=
    allFin_pending_field_zero rate candidate candidate.gammaLoc (by
      intro b hb
      have hbParts := (hArmAfter b).mp hb
      have hzero := (allFin_eq_true_iff _).1 hgammaPending b
      have hcheck : armPendingCheck s b = true :=
        (armPendingCheck_eq_true_iff rate s b).2 hbParts.2
      have hbool := by simpa [hcheck] using hzero
      have hzeroInput : s.gammaLoc b = 0 := hbool
      simpa [candidate, acceptUpCandidate] using hzeroInput)
  have hincrementPendingAfter : allFin p.K (fun b =>
      (!armPendingCheck candidate b) || decide (candidate.increment b = 0)) = true :=
    allFin_pending_field_zero rate candidate candidate.increment (by
      intro b hb
      have hbParts := (hArmAfter b).mp hb
      have hzero := (allFin_eq_true_iff _).1 hincrementPending b
      have hcheck : armPendingCheck s b = true :=
        (armPendingCheck_eq_true_iff rate s b).2 hbParts.2
      have hbool := by simpa [hcheck] using hzero
      have hincInput : s.increment b = 0 := hbool
      have hframe : candidate.increment b = s.increment b := by
        simp [candidate, acceptUpCandidate, a, hbParts.1]
      exact hframe.trans hincInput)
  have hcurrentDomainInput : ∀ b q, s.currentRegisters b = some q →
      q.queue ≤ p.T * D p ∧ q.lastService ≤ D p := by
    intro b q hq
    have hb := (allFin_eq_true_iff _).1 hcurrentOld b
    simp [hq, Bool.and_eq_true, decide_eq_true_eq] at hb
    exact hb
  have hcutoffDomainInput : ∀ b z, s.cutoffRegisters b = some z →
      z.score ≤ p.T * D p ∧ z.queue ≤ p.T * D p ∧ z.lastService ≤ D p := by
    intro b z hz
    have hb := (allFin_eq_true_iff _).1 hcutoffOld b
    simp [hz, Bool.and_eq_true, decide_eq_true_eq] at hb
    rcases hb with ⟨⟨hs, hq⟩, hl⟩
    exact ⟨hs, hq, hl⟩
  have hincrementDomainInput : ∀ b, s.increment b ≤ p.T * D p := by
    intro b
    exact of_decide_eq_true ((allFin_eq_true_iff _).1 hincrementOld b)
  have hgammaDomainInput : ∀ b, s.gammaLoc b ≤ D p := by
    intro b
    exact of_decide_eq_true ((allFin_eq_true_iff _).1 hgammaOld b)
  have hbaseDomainInput : ∀ j, s.baseScore j ≤ p.T * D p := by
    intro j
    exact of_decide_eq_true ((allFin_eq_true_iff _).1 hbaseOld j)
  have hcurrentDomainAfter : ∀ b q, candidate.currentRegisters b = some q →
      q.queue ≤ p.T * D p ∧ q.lastService ≤ D p := by
    intro b q hq
    by_cases hba : b = a
    · subst b
      have hqEq : q = ⟨(QueueReplay.replay (4 * rate.n) (0, U.val.q) records).2,
          (QueueReplay.replay (4 * rate.n) (0, U.val.q) records).1 -
            (QueueReplay.replay (4 * rate.n) (0, U.val.q)
              (records.take (records.length - 1))).1⟩ :=
        (Option.some.inj (hcurrentRecovered.symm.trans hq)).symm
      subst q
      have hqueue : (QueueReplay.replay (4 * rate.n) (0, U.val.q) records).2 ≤
          p.T * D p := by omega
      exact ⟨hqueue, by simpa using hfinalServiceFull.trans hfourN⟩
    · have hqOld : s.currentRegisters b = some q := by
        have hframe : candidate.currentRegisters b = s.currentRegisters b := by
          simp [candidate, acceptUpCandidate, a, hba]
        exact hframe.symm.trans hq
      exact hcurrentDomainInput b q hqOld
  have hcutoffDomainAfter : ∀ b z, candidate.cutoffRegisters b = some z →
      z.score ≤ p.T * D p ∧ z.queue ≤ p.T * D p ∧ z.lastService ≤ D p := by
    intro b z hz
    by_cases hba : b = a
    · subst b
      have hzEq : z = ⟨s.baseScore i + U.val.S, U.val.q, U.val.delta⟩ :=
        (Option.some.inj (hcutoffRecovered.symm.trans hz)).symm
      subst z
      have hscore : s.baseScore i + U.val.S ≤ p.T * D p := by
        have hmul := Nat.mul_le_mul_right (D p) hcutoffLeT
        omega
      exact ⟨hscore, hqBound, hdelta⟩
    · have hzOld : s.cutoffRegisters b = some z := by
        have hframe : candidate.cutoffRegisters b = s.cutoffRegisters b := by
          simp [candidate, acceptUpCandidate, a, hba]
        exact hframe.symm.trans hz
      exact hcutoffDomainInput b z hzOld
  have hcurrentDomainsAfter : allFin p.K (fun b =>
      match candidate.currentRegisters b with
      | none => true
      | some q => decide (q.queue ≤ p.T * D p) &&
          decide (q.lastService ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro b
    cases hq : candidate.currentRegisters b with
    | none => simp
    | some q => simp [hcurrentDomainAfter b q hq]
  have hcutoffDomainsAfter : allFin p.K (fun b =>
      match candidate.cutoffRegisters b with
      | none => true
      | some z => decide (z.score ≤ p.T * D p) &&
          decide (z.queue ≤ p.T * D p) && decide (z.lastService ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro b
    cases hz : candidate.cutoffRegisters b with
    | none => simp
    | some z => simp [hcutoffDomainAfter b z hz]
  have hbaseDomainsAfter : allFin (p.m - 1)
      (fun j => decide (candidate.baseScore j ≤ p.T * D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro j
    exact decide_eq_true (hbaseDomainInput j)
  have hincrementDomainsAfter : allFin p.K
      (fun b => decide (candidate.increment b ≤ p.T * D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro b
    by_cases hba : b = a
    · subst b
      rw [hincrementRecovered]
      exact decide_eq_true (by omega)
    · have hframe : candidate.increment b = s.increment b := by
        simp [candidate, acceptUpCandidate, a, hba]
      rw [hframe]
      exact decide_eq_true (hincrementDomainInput b)
  have hgammaDomainsAfter : allFin p.K
      (fun b => decide (candidate.gammaLoc b ≤ D p)) = true := by
    apply (allFin_eq_true_iff _).2
    intro b
    exact decide_eq_true (hgammaDomainInput b)
  have hregisterDomainsAfter : registerDomainsCheck candidate = true := by
    simp only [registerDomainsCheck, Bool.and_eq_true]
    exact ⟨⟨⟨⟨hcurrentDomainsAfter, hcutoffDomainsAfter⟩,
      hbaseDomainsAfter⟩, hincrementDomainsAfter⟩, hgammaDomainsAfter⟩
  have hrawSupportAfter : ∀ b r amount, candidate.rawBuffer b r = some amount →
      0 < amount ∧ amount ≤ D p ∧ candidate.cutoff ≤ sourceRound r ∧
        sourceRound r < candidate.freezeAt ∧ sourceRound r ≤ candidate.cursor ∧
        armPending candidate b := by
    intro b r amount hcell
    by_cases hba : b = a
    · subst b
      have hclear : candidate.rawBuffer a r = none := by
        simp [candidate, acceptUpCandidate, clearRawArm, a]
      rw [hclear] at hcell
      cases hcell
    · have hcellOld : s.rawBuffer b r = some amount := by
        have hframe : candidate.rawBuffer b r = s.rawBuffer b r := by
          simp [candidate, acceptUpCandidate, clearRawArm, a, hba]
        exact hframe.symm.trans hcell
      obtain ⟨hpos, hD, hcut, hfreeze, htime, hpending⟩ := hrawPoint b r amount hcellOld
      have hpendingOld : armPending s b :=
        (armPendingCheck_eq_true_iff rate s b).1 hpending
      have hpendingNew : armPending candidate b :=
        (hArmAfter b).2 ⟨hba, hpendingOld⟩
      exact ⟨hpos, hD, by simpa [candidate, acceptUpCandidate] using hcut,
        by simpa [candidate, acceptUpCandidate] using hfreeze,
        by simpa [candidate, acceptUpCandidate] using htime, hpendingNew⟩
  have hrawDomainsAfter : rawEntryDomainsCheck candidate = true := by
    unfold rawEntryDomainsCheck
    apply (allFin_eq_true_iff _).2
    intro b
    apply (allFin_eq_true_iff _).2
    intro r
    cases hcell : candidate.rawBuffer b r with
    | none => rfl
    | some amount =>
        obtain ⟨hpos, hD, hcut, hfreeze, htime, hpending⟩ :=
          hrawSupportAfter b r amount hcell
        have hcheck : armPendingCheck candidate b = true :=
          (armPendingCheck_eq_true_iff rate candidate b).2 hpending
        have hnotReady : candidate.phase ≠ Phase.ready := by
          simp [candidate, acceptUpCandidate]
        simp [hpos, hD, hcut, hfreeze, htime, hcheck, hnotReady]
  have hstartedHistoryAfter : startedHistoryCheck candidate = true := by
    simpa [startedHistoryCheck, candidate, acceptUpCandidate] using hhistory
  have htimeAfter :
      1 ≤ candidate.sigma ∧ candidate.sigma ≤ p.T ∧
      1 ≤ candidate.cutoff ∧ candidate.cutoff ≤ candidate.freezeAt ∧
      candidate.cutoff ≤ p.T ∧ candidate.freezeAt ≤ p.T + 1 ∧
      candidate.cutoff ≤ candidate.cursor ∧ candidate.cursor ≤ p.T + 1 ∧
      candidate.cursor ≤ p.T := by
    change 1 ≤ s.sigma ∧ s.sigma ≤ p.T ∧
      1 ≤ s.cutoff ∧ s.cutoff ≤ s.freezeAt ∧ s.cutoff ≤ p.T ∧
      s.freezeAt ≤ p.T + 1 ∧ s.cutoff ≤ s.cursor ∧
      s.cursor ≤ p.T + 1 ∧ s.cursor ≤ p.T
    exact ⟨hsigmaPosCheck, hsigmaTCheck,
      hcutPos, hcutFreezeCheck, hcutoffLeT,
      hfreezeTCheck, hcutCursor, hcursorLeTPlus, hcursorLeT'⟩
  have hcandidateValid : validLedgerCheck candidate = true := by
    have hreadyFalse : decide (candidate.phase = Phase.ready) = false := by
      simp [candidate, acceptUpCandidate]
    rcases htimeAfter with ⟨hsigmaPos, hsigmaT, hcutPos', hcutFreeze',
      hcutT', hfreezeT', hcutCursor', hcursorTPlus, hcursorT'⟩
    simp [validLedgerCheck, hreadyFalse, decide_eq_true hsigmaPos,
      decide_eq_true hsigmaT, decide_eq_true hcutPos', decide_eq_true hcutFreeze',
      decide_eq_true hcutT', decide_eq_true hfreezeT', decide_eq_true hcutCursor',
      decide_eq_true hcursorTPlus, decide_eq_true hcursorT',
      hstartedHistoryAfter, hcurrentPendingAfter, hcutoffPendingAfter,
      hgammaPendingAfter, hincrementPendingAfter, hregisterDomainsAfter,
      hrawDomainsAfter]
  refine ⟨hs, hc, past, current, hPast, hCurrent, hrecordsLength,
    ?_, ?_, ?_, ?_⟩
  · exact hout
  · simpa [candidate] using hcandidateValid
  · intro h hh
    exact ⟨hprefixMass h hh, hprefixBound h hh⟩
  · exact ⟨by simpa [records] using hfinalServiceFull, hfourN⟩

end Bandits.Support.ReferenceCompleteCollectionUpDecodeDomains

end
