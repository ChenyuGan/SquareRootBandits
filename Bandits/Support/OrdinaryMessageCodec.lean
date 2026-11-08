/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Ordinary DOWN and UP message records and codec

This module implements the ordinary record carriers, five-block binary
encoding, and deterministic parsers from
`sources/zip4/manuscript/06_interruptions.tex:103-189` and
`sources/zip4/manuscript/05_binary_transport.tex:11-21`.
The block order is the order in the manuscript. Within a block, bit zero is
the least significant bit. `wordEquivFlat` identifies the five-block
representation exactly with a `Fin (5 * L) → ZMod 2` word.

Acceptance checks only the record carrier and the stated local fields. They do
not certify that an accepted message was sent on the channel.
-/

public section

namespace Bandits.Support.OrdinaryMessageCodec

/-- Codec inputs, including the source-valid size relations used by this module. -/
structure CodecParams where
  m : Nat
  K : Nat
  T : Nat
  D : Nat
  bN : Nat
  beta : Real
  hT : 0 < T
  hD : 0 < D
  hKD : K ≤ D
  hbN : bN ≤ D

/-- The fixed field width `ceil(log₂(TD + 1))`, expressed by `Nat.clog`. -/
@[expose] def fieldWidth (T D : Nat) : Nat := Nat.clog 2 (T * D + 1)

/-- The dyadic value represented by the DOWN exponent `h`. -/
@[expose] noncomputable def dyadicRate (h : Nat) : Real := ((2 : Real) ^ h)⁻¹

/-- A DOWN record before its admissibility proof is attached. -/
@[ext] structure DownFields where
  sigma : Nat
  a : Nat
  e : Nat
  h : Nat
  q : Nat
  deriving DecidableEq

/-- A UP record before its admissibility proof is attached. -/
@[ext] structure UpFields where
  sigma : Nat
  S : Nat
  delta : Nat
  q : Nat
  deriving DecidableEq

/-- The literal admissibility predicate for ordinary DOWN records. -/
@[expose] noncomputable def downAdmissible (p : CodecParams) (x : DownFields) : Prop :=
  1 ≤ x.sigma ∧ x.sigma ≤ p.T ∧
  1 ≤ x.a ∧ x.a ≤ p.K ∧ 1 ≤ x.e ∧ x.e ≤ p.K ∧ x.a ≠ x.e ∧
  x.h ≤ p.bN ∧ p.beta ≤ dyadicRate x.h ∧
  dyadicRate x.h ≤ 1 / ((16 : Real) * (p.m : Real) * (p.K : Real)) ∧
  x.q ≤ p.T * p.D

/-- The distinguished empty UP offer `(0,0,0,0)`. -/
@[expose] def upPlaceholder : UpFields := ⟨0, 0, 0, 0⟩

/-- The literal UP domain: the placeholder, or the source four-field box. -/
@[expose] def upAdmissible (p : CodecParams) (x : UpFields) : Prop :=
  x = upPlaceholder ∨
    (1 ≤ x.sigma ∧ x.sigma ≤ p.T ∧ x.S ≤ p.T * p.D ∧
      x.delta ≤ p.D ∧ x.q ≤ p.T * p.D)

/-- The subtype of source-admissible ordinary DOWN records. -/
@[expose] noncomputable def DownRecord (p : CodecParams) : Type :=
  {x : DownFields // downAdmissible p x}

/-- The subtype of source-admissible ordinary UP records. -/
@[expose] def UpRecord (p : CodecParams) : Type :=
  {x : UpFields // upAdmissible p x}

/-- `TD + 1` is at most the power selected by the ceiling logarithm. -/
theorem td_add_one_le_two_pow_fieldWidth (p : CodecParams) :
    p.T * p.D + 1 ≤ 2 ^ fieldWidth p.T p.D := by
  exact Nat.le_pow_clog (by decide) _

/-- The maximum record field `TD` fits in the literal width. -/
theorem td_lt_two_pow_fieldWidth (p : CodecParams) :
    p.T * p.D < 2 ^ fieldWidth p.T p.D := by
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (td_add_one_le_two_pow_fieldWidth p)

theorem T_le_T_mul_D (p : CodecParams) : p.T ≤ p.T * p.D := by
  calc
    p.T = p.T * 1 := by simp
    _ ≤ p.T * p.D := Nat.mul_le_mul_left p.T (Nat.succ_le_of_lt p.hD)

theorem D_le_T_mul_D (p : CodecParams) : p.D ≤ p.T * p.D := by
  calc
    p.D = 1 * p.D := by simp
    _ ≤ p.T * p.D := Nat.mul_le_mul_right p.D (Nat.succ_le_of_lt p.hT)

/-- Any natural field bounded by `TD` fits in an `L`-bit block. -/
theorem field_fits_of_le_td (p : CodecParams) {x : Nat} (hx : x ≤ p.T * p.D) :
    x < 2 ^ fieldWidth p.T p.D :=
  Nat.lt_of_le_of_lt hx (td_lt_two_pow_fieldWidth p)

/-- Every value in an admissible DOWN record fits in its encoded field. -/
theorem down_fields_fit (p : CodecParams) (x : DownRecord p) :
    x.val.sigma < 2 ^ fieldWidth p.T p.D ∧
    x.val.a < 2 ^ fieldWidth p.T p.D ∧
    x.val.e < 2 ^ fieldWidth p.T p.D ∧
    x.val.h < 2 ^ fieldWidth p.T p.D ∧
    x.val.q < 2 ^ fieldWidth p.T p.D := by
  rcases x.property with
    ⟨hsigma_lo, hsigma_hi, ha_lo, ha_hi, he_lo, he_hi, hae, hh, hbeta_lo,
      hbeta_hi, hq⟩
  have hTtd := T_le_T_mul_D p
  have hDtd := D_le_T_mul_D p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact field_fits_of_le_td p (hsigma_hi.trans hTtd)
  · exact field_fits_of_le_td p ((ha_hi.trans p.hKD).trans hDtd)
  · exact field_fits_of_le_td p ((he_hi.trans p.hKD).trans hDtd)
  · exact field_fits_of_le_td p ((hh.trans p.hbN).trans hDtd)
  · exact field_fits_of_le_td p hq

/-- Every value in an admissible UP record, including the placeholder, fits. -/
theorem up_fields_fit (p : CodecParams) (x : UpRecord p) :
    x.val.sigma < 2 ^ fieldWidth p.T p.D ∧
    x.val.S < 2 ^ fieldWidth p.T p.D ∧
    x.val.delta < 2 ^ fieldWidth p.T p.D ∧
    x.val.q < 2 ^ fieldWidth p.T p.D := by
  have hzero : 0 < 2 ^ fieldWidth p.T p.D := Nat.pow_pos (by decide)
  rcases x with ⟨fields, hfields⟩
  rcases hfields with hplaceholder | ⟨hsigma_lo, hsigma_hi, hS, hdelta, hq⟩
  · subst fields
    exact ⟨hzero, hzero, hzero, hzero⟩
  · have hTtd := T_le_T_mul_D p
    have hDtd := D_le_T_mul_D p
    exact ⟨field_fits_of_le_td p (hsigma_hi.trans hTtd),
      field_fits_of_le_td p hS, field_fits_of_le_td p (hdelta.trans hDtd),
      field_fits_of_le_td p hq⟩

/-- One fixed-width block, with bit positions in least-significant-first order. -/
@[expose] def WordBlock (L : Nat) := Fin L → ZMod 2

/-- Five consecutive `L`-bit fields, in source order. -/
@[expose] def Word (p : CodecParams) := Fin 5 → WordBlock (fieldWidth p.T p.D)

/-- Flatten the five blocks using position `block * L + bit`. -/
@[expose] def wordEquivFlat (p : CodecParams) :
    Word p ≃ (Fin (5 * fieldWidth p.T p.D) → ZMod 2) where
  toFun w j :=
    let e := finProdFinEquiv (m := 5) (n := fieldWidth p.T p.D)
    let blockBit := e.symm j
    w blockBit.1 blockBit.2
  invFun w b i :=
    w (finProdFinEquiv (m := 5) (n := fieldWidth p.T p.D) (b, i))
  left_inv w := by
    funext b i
    let e := finProdFinEquiv (m := 5) (n := fieldWidth p.T p.D)
    change w (e.symm (e (b, i))).1 (e.symm (e (b, i))).2 = w b i
    exact congrArg (fun z : Fin 5 × Fin (fieldWidth p.T p.D) => w z.1 z.2)
      (e.symm_apply_apply (b, i))
  right_inv w := by
    funext j
    let e := finProdFinEquiv (m := 5) (n := fieldWidth p.T p.D)
    change w (e (e.symm j)) = w j
    exact congrArg w (e.apply_symm_apply j)

/-- Encode a natural number as an `L`-bit block, least-significant bit first. -/
@[expose] def encodeField (L x : Nat) : WordBlock L := fun i =>
  if x.testBit i.val then 1 else 0

/-- Decode a field by the standard little-endian natural-number bit constructor. -/
@[expose] def decodeField (L : Nat) (bits : WordBlock L) : Nat :=
  Nat.ofBits (fun i => decide (bits i = 1))

theorem decodeField_encodeField (L x : Nat) (hx : x < 2 ^ L) :
    decodeField L (encodeField L x) = x := by
  unfold decodeField
  have hbits : (fun i : Fin L => decide (encodeField L x i = 1)) =
      fun i : Fin L => x.testBit i.val := by
    funext i
    simp [encodeField]
  rw [hbits, Nat.ofBits_testBit, Nat.mod_eq_of_lt hx]

theorem encodeBit_decodeBit (z : ZMod 2) :
    (if decide (z = 1) then (1 : ZMod 2) else 0) = z := by
  have hzval := ZMod.val_lt z
  have hcases : z.val = 0 ∨ z.val = 1 := by omega
  rcases hcases with hzero | hone
  · have hz : z = 0 := by
      have hzcast := ZMod.natCast_zmod_val z
      rw [hzero] at hzcast
      exact hzcast.symm
    simp [hz]
  · have hz : z = 1 := by
      have hzcast := ZMod.natCast_zmod_val z
      rw [hone] at hzcast
      exact hzcast.symm
    simp [hz]

theorem encodeField_decodeField (L : Nat) (bits : WordBlock L) :
    encodeField L (decodeField L bits) = bits := by
  funext i
  unfold encodeField decodeField
  rw [Nat.testBit_ofBits_lt (fun j : Fin L => decide (bits j = 1)) i.val i.isLt]
  exact encodeBit_decodeBit (bits i)

/-- The value in one of five ordered blocks. -/
@[expose] def fiveField (x0 x1 x2 x3 x4 : Nat) (b : Fin 5) : Nat :=
  if b.val = 0 then x0 else if b.val = 1 then x1 else if b.val = 2 then x2
    else if b.val = 3 then x3 else x4

/-- Encode five natural fields into the five consecutive blocks. -/
@[expose] def encodeFive (L : Nat) (x0 x1 x2 x3 x4 : Nat) : Fin 5 → WordBlock L :=
  fun b => encodeField L (fiveField x0 x1 x2 x3 x4 b)

/-- Deterministically decode the five block values. -/
@[expose] def decodeFive (L : Nat) (w : Fin 5 → WordBlock L) : Fin 5 → Nat :=
  fun b => decodeField L (w b)

theorem decodeFive_encodeFive (L x0 x1 x2 x3 x4 : Nat)
    (h0 : x0 < 2 ^ L) (h1 : x1 < 2 ^ L) (h2 : x2 < 2 ^ L)
    (h3 : x3 < 2 ^ L) (h4 : x4 < 2 ^ L) :
    decodeFive L (encodeFive L x0 x1 x2 x3 x4) = fiveField x0 x1 x2 x3 x4 := by
  funext b
  fin_cases b <;>
    simp [decodeFive, encodeFive, fiveField, decodeField_encodeField, h0, h1, h2, h3, h4]

theorem encodeFive_decodeFive (L : Nat) (w : Fin 5 → WordBlock L) :
    encodeFive L (decodeFive L w 0) (decodeFive L w 1) (decodeFive L w 2)
      (decodeFive L w 3) (decodeFive L w 4) = w := by
  funext b i
  fin_cases b <;> simp [encodeFive, fiveField, decodeFive, encodeField_decodeField]

/-- Decode all five word blocks into a DOWN-shaped record. -/
@[expose] def downFieldsOfWord (p : CodecParams) (w : Word p) : DownFields :=
  ⟨decodeField (fieldWidth p.T p.D) (w 0), decodeField (fieldWidth p.T p.D) (w 1),
    decodeField (fieldWidth p.T p.D) (w 2), decodeField (fieldWidth p.T p.D) (w 3),
    decodeField (fieldWidth p.T p.D) (w 4)⟩

/-- Decode the first four word blocks into an UP-shaped record. -/
@[expose] def upFieldsOfWord (p : CodecParams) (w : Word p) : UpFields :=
  ⟨decodeField (fieldWidth p.T p.D) (w 0), decodeField (fieldWidth p.T p.D) (w 1),
    decodeField (fieldWidth p.T p.D) (w 2), decodeField (fieldWidth p.T p.D) (w 3)⟩

/-- Encode an admissible DOWN record in the five source blocks `sigma,a,e,h,q`. -/
@[expose] def encodeDown (p : CodecParams) (x : DownRecord p) : Word p :=
  encodeFive (fieldWidth p.T p.D) x.val.sigma x.val.a x.val.e x.val.h x.val.q

/-- Encode an UP record in the blocks `sigma,S,delta,q,zero`. -/
@[expose] def encodeUp (p : CodecParams) (x : UpRecord p) : Word p :=
  encodeFive (fieldWidth p.T p.D) x.val.sigma x.val.S x.val.delta x.val.q 0

/-- A DOWN encoder round-trips through all five deterministic block decoders. -/
theorem downFieldsOfWord_encodeDown (p : CodecParams) (x : DownRecord p) :
    downFieldsOfWord p (encodeDown p x) = x.val := by
  rcases x with ⟨⟨sigma, a, e, h, q⟩, hx⟩
  rcases down_fields_fit p ⟨⟨sigma, a, e, h, q⟩, hx⟩ with
    ⟨hsigma, ha, he, hh, hq⟩
  apply DownFields.ext
  · simp [downFieldsOfWord, encodeDown, encodeFive, fiveField, decodeField_encodeField, hsigma]
  · simp [downFieldsOfWord, encodeDown, encodeFive, fiveField, decodeField_encodeField, ha]
  · simp [downFieldsOfWord, encodeDown, encodeFive, fiveField, decodeField_encodeField, he]
  · simp [downFieldsOfWord, encodeDown, encodeFive, fiveField, decodeField_encodeField, hh]
  · simp [downFieldsOfWord, encodeDown, encodeFive, fiveField, decodeField_encodeField, hq]

/-- An UP encoder round-trips through its four record fields. -/
theorem upFieldsOfWord_encodeUp (p : CodecParams) (x : UpRecord p) :
    upFieldsOfWord p (encodeUp p x) = x.val := by
  rcases x with ⟨⟨sigma, S, delta, q⟩, hx⟩
  rcases up_fields_fit p ⟨⟨sigma, S, delta, q⟩, hx⟩ with
    ⟨hsigma, hS, hdelta, hq⟩
  have hzero : 0 < 2 ^ fieldWidth p.T p.D := Nat.pow_pos (by decide)
  apply UpFields.ext
  · simp [upFieldsOfWord, encodeUp, encodeFive, fiveField, decodeField_encodeField, hsigma]
  · simp [upFieldsOfWord, encodeUp, encodeFive, fiveField, decodeField_encodeField, hS]
  · simp [upFieldsOfWord, encodeUp, encodeFive, fiveField, decodeField_encodeField, hdelta]
  · simp [upFieldsOfWord, encodeUp, encodeFive, fiveField, decodeField_encodeField, hq]

/-- Parse an optional DOWN word by decoding then checking admissibility and exact re-encoding. -/
@[expose] noncomputable def parseDown (p : CodecParams) (w : Option (Word p)) : Option (DownRecord p) := by
  classical
  exact
  match w with
  | none => none
  | some bits =>
    let fields := downFieldsOfWord p bits
    if hadm : downAdmissible p fields then
      let record : DownRecord p := ⟨fields, hadm⟩
      if hencode : encodeDown p record = bits then some record else none
    else none

/-- Parse an optional UP word by decoding then checking admissibility and exact re-encoding. -/
@[expose] noncomputable def parseUp (p : CodecParams) (w : Option (Word p)) : Option (UpRecord p) := by
  classical
  exact
  match w with
  | none => none
  | some bits =>
    let fields := upFieldsOfWord p bits
    if hadm : upAdmissible p fields then
      let record : UpRecord p := ⟨fields, hadm⟩
      if hencode : encodeUp p record = bits then some record else none
    else none

theorem parseDown_encode (p : CodecParams) (x : DownRecord p) :
    parseDown p (some (encodeDown p x)) = some x := by
  classical
  rw [parseDown, downFieldsOfWord_encodeDown]
  rw [dite_eq_left x.property]
  have hrecord : (⟨x.val, x.property⟩ : DownRecord p) = x := Subtype.ext rfl
  simp [hrecord]

theorem parseUp_encode (p : CodecParams) (x : UpRecord p) :
    parseUp p (some (encodeUp p x)) = some x := by
  classical
  rw [parseUp, upFieldsOfWord_encodeUp]
  rw [dite_eq_left x.property]
  have hrecord : (⟨x.val, x.property⟩ : UpRecord p) = x := Subtype.ext rfl
  simp [hrecord]

theorem parseDown_some_sound (p : CodecParams) {bits : Word p}
    {x : DownRecord p} (h : parseDown p (some bits) = some x) :
    bits = encodeDown p x := by
  simp only [parseDown] at h
  split_ifs at h with hadm hencode
  · injection h with hx
    subst x
    exact hencode.symm

theorem parseUp_some_sound (p : CodecParams) {bits : Word p}
    {x : UpRecord p} (h : parseUp p (some bits) = some x) :
    bits = encodeUp p x := by
  simp only [parseUp] at h
  split_ifs at h with hadm hencode
  · injection h with hx
    subst x
    exact hencode.symm

/-- Every encoded UP word has an all-zero fifth (padding) block. -/
theorem encodeUp_padding (p : CodecParams) (x : UpRecord p) (i : Fin (fieldWidth p.T p.D)) :
    encodeUp p x 4 i = 0 := by
  simp [encodeUp, encodeFive, fiveField, encodeField]

/-- A nonzero fifth block is rejected by the UP parser. -/
theorem parseUp_rejects_nonzero_padding (p : CodecParams) (bits : Word p)
    (i : Fin (fieldWidth p.T p.D)) (hi : bits 4 i ≠ 0) :
    parseUp p (some bits) = none := by
  cases hparse : parseUp p (some bits) with
  | none => rfl
  | some x =>
    have hencoded := parseUp_some_sound p hparse
    have hzero : bits 4 i = 0 := by
      rw [hencoded]
      exact encodeUp_padding p x i
    exact False.elim (hi hzero)

/-- The direction selected by the public communication slot. -/
inductive Direction where
  | DOWN
  | UP
  deriving DecidableEq

/-- Direction-indexed subtype of source-admissible records. -/
@[expose] def MessageRecord (p : CodecParams) : Direction → Type
  | .DOWN => DownRecord p
  | .UP => UpRecord p

/-- Direction-indexed ordinary message encoding. -/
@[expose] def encode (p : CodecParams) : (dir : Direction) → MessageRecord p dir → Word p
  | .DOWN, x => encodeDown p x
  | .UP, x => encodeUp p x

/-- Direction-indexed deterministic parser. -/
@[expose] noncomputable def parseDir (p : CodecParams) : (dir : Direction) → Option (Word p) →
    Option (MessageRecord p dir)
  | .DOWN, w => parseDown p w
  | .UP, w => parseUp p w

/-- Parsing an encoded admissible record returns that record exactly. -/
theorem parseDir_encode (p : CodecParams) (dir : Direction)
    (x : MessageRecord p dir) :
    parseDir p dir (some (encode p dir x)) = some x := by
  cases dir with
  | DOWN => exact parseDown_encode p x
  | UP => exact parseUp_encode p x

/-- Any successful parse is exactly the record encoded by its input word. -/
theorem parseDir_some_sound (p : CodecParams) (dir : Direction) (w : Option (Word p))
    (x : MessageRecord p dir) (h : parseDir p dir w = some x) :
    w = some (encode p dir x) := by
  cases dir with
  | DOWN =>
    cases w with
    | none => simp_all [parseDir, parseDown]
    | some bits =>
      have h' : parseDown p (some bits) = some x := by simpa [parseDir, MessageRecord] using h
      have he := parseDown_some_sound p h'
      exact congrArg Option.some he
  | UP =>
    cases w with
    | none => simp_all [parseDir, parseUp]
    | some bits =>
      have h' : parseUp p (some bits) = some x := by simpa [parseDir, MessageRecord] using h
      have he := parseUp_some_sound p h'
      exact congrArg Option.some he

/-- The parser returns `none` exactly on `none` and words outside the image. -/
theorem parseDir_none_iff_nonimage (p : CodecParams) (dir : Direction)
    (w : Option (Word p)) :
    parseDir p dir w = none ↔
      ¬ ∃ x : MessageRecord p dir, w = some (encode p dir x) := by
  constructor
  · intro h ⟨x, hx⟩
    rw [hx, parseDir_encode] at h
    cases h
  · intro h
    cases hparse : parseDir p dir w with
    | none => rfl
    | some x =>
      have hw := parseDir_some_sound p dir w x hparse
      exact False.elim (h ⟨x, hw⟩)

/-- Encoding is injective because parsing is a left inverse on admissible records. -/
theorem encode_injective (p : CodecParams) (dir : Direction) :
    Function.Injective (encode p dir) := by
  intro x y hxy
  have hp := congrArg (fun w => parseDir p dir (some w)) hxy
  rw [parseDir_encode, parseDir_encode] at hp
  exact Option.some.inj hp

/-- DOWN acceptance is precisely `sigmaOld < M.sigma ≤ t` on the carrier. -/
@[expose] def acceptDown (p : CodecParams) (sigmaOld t : Nat)
    (M : DownRecord p) : Prop :=
  sigmaOld < M.val.sigma ∧ M.val.sigma ≤ t

/-- UP acceptance checks the cutoff, pending membership, and current assignment sigma. -/
@[expose] def acceptUp (p : CodecParams) (u t follower : Nat) (P : Set Nat)
    (sigmaCurrent : Nat) (M : UpRecord p) : Prop :=
  u ≤ t ∧ follower ∈ P ∧ M.val.sigma = sigmaCurrent

end Bandits.Support.OrdinaryMessageCodec

end
