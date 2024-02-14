/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/
import Std.Data.Bool
import Std.Data.BitVec.Basic
import Std.Data.Fin.Lemmas
import Std.Data.Nat.Lemmas

import Std.Tactic.Ext
import Std.Tactic.Simpa
import Std.Tactic.Omega
import Std.Util.ProofWanted

namespace Std.BitVec

-- We use variables `w`, `v` and `u` (in order of preference) to represent the width of a bitvector
variable {w v u : Nat}

/-- Prove equality of bitvectors in terms of nat operations. -/
theorem eq_of_toNat_eq : ∀ {i j : BitVec w}, i.toNat = j.toNat → i = j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- Replaced 2024-02-07. -/
@[deprecated] alias zero_is_unique := eq_nil

@[simp] theorem val_toFin (x : BitVec w) : x.toFin.val = x.toNat := rfl

theorem toNat_eq (x y : BitVec w) : x = y ↔ x.toNat = y.toNat :=
  Iff.intro (congrArg BitVec.toNat) eq_of_toNat_eq

theorem toNat_lt (x : BitVec w) : x.toNat < 2^w := x.toFin.2

theorem testBit_toNat (x : BitVec w) : x.toNat.testBit i = x.getLsb i := rfl

@[simp] theorem getLsb_ofFin (x : Fin (2^w)) (i : Nat) :
  getLsb (BitVec.ofFin x) i = x.val.testBit i := rfl

@[simp] theorem getLsb_ge (x : BitVec w) (i : Nat) (ge : i ≥ w) : getLsb x i = false := by
  let ⟨x, x_lt⟩ := x
  simp
  apply Nat.testBit_lt_two_pow
  have p : 2^w ≤ 2^i := Nat.pow_le_pow_of_le_right (by omega) ge
  omega

theorem lt_of_getLsb (x : BitVec w) (i : Nat) : getLsb x i = true → i < w := by
  if h : i < w then
    simp [h]
  else
    simp [Nat.ge_of_not_lt h]

-- We choose `eq_of_getLsb_eq` as the `@[ext]` theorem for `BitVec`
-- somewhat arbitrarily over `eq_of_getMsg_eq`.
@[ext] theorem eq_of_getLsb_eq {x y : BitVec w}
    (pred : ∀(i : Fin w), x.getLsb i.val = y.getLsb i.val) : x = y := by
  apply eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro i
  if i_lt : i < w then
    exact pred ⟨i, i_lt⟩
  else
    have p : i ≥ w := Nat.le_of_not_gt i_lt
    simp [testBit_toNat, getLsb_ge _ _ p]

theorem eq_of_getMsb_eq {x y : BitVec w}
    (pred : ∀(i : Fin w), x.getMsb i = y.getMsb i.val) : x = y := by
  simp only [getMsb] at pred
  apply eq_of_getLsb_eq
  intro ⟨i, i_lt⟩
  if w_zero : w = 0 then
    simp [w_zero]
  else
    have w_pos := Nat.pos_of_ne_zero w_zero
    have r : i ≤ w - 1 := by
      simp [Nat.le_sub_iff_add_le w_pos, Nat.add_succ]
      exact i_lt
    have q_lt : w - 1 - i < w := by
      simp only [Nat.sub_sub]
      apply Nat.sub_lt w_pos
      simp [Nat.succ_add]
    have q := pred ⟨w - 1 - i, q_lt⟩
    simpa [q_lt, Nat.sub_sub_self, r] using q

theorem eq_of_toFin_eq {x y : BitVec w} (w : x.toFin = y.toFin) : x = y := by
  ext
  simp only [← testBit_toNat, ← val_toFin, w]

@[simp] theorem toNat_ofBool (b : Bool) : (ofBool b).toNat = b.toNat := by
  cases b <;> rfl

theorem ofNat_one (w : Nat) : BitVec.ofNat 1 w = BitVec.ofBool (w % 2 = 1) :=  by
  rcases (Nat.mod_two_eq_zero_or_one w) with h | h <;> simp [h, BitVec.ofNat, Fin.ofNat']

@[simp] theorem toNat_ofFin (x : Fin (2^w)) : (BitVec.ofFin x).toNat = x.val := rfl

@[simp] theorem toNat_ofNat (x w : Nat) : (x#w).toNat = x % 2^w := by
  simp [BitVec.toNat, BitVec.ofNat, Fin.ofNat']

@[simp] theorem getLsb_ofNat (n : Nat) (x : Nat) (i : Nat) :
  getLsb (x#n) i = (i < n && x.testBit i) := by
  simp [getLsb, BitVec.ofNat, Fin.val_ofNat']

@[deprecated toNat_ofNat] theorem toNat_zero (n : Nat) : (0#n).toNat = 0 := by trivial

@[simp] theorem toNat_mod_cancel (x : BitVec w) : x.toNat % (2^w) = x.toNat :=
  Nat.mod_eq_of_lt x.isLt

private theorem lt_two_pow_of_le {x m n : Nat} (lt : x < 2 ^ m) (le : m ≤ n) : x < 2 ^ n :=
  Nat.lt_of_lt_of_le lt (Nat.pow_le_pow_of_le_right (by trivial : 0 < 2) le)

@[simp] theorem ofNat_toNat (v : Nat) (x : BitVec w) : x.toNat#v = truncate v x := by
  let ⟨x, lt_w⟩ := x
  unfold truncate
  unfold zeroExtend
  if h : w ≤ v then
    unfold zeroExtend'
    have lt_v : x < 2 ^ v := lt_two_pow_of_le lt_w h
    simp [h, lt_v, Nat.mod_eq_of_lt, BitVec.toNat, BitVec.ofNat, Fin.ofNat']
  else
    simp [h]

/-! ### cast -/

@[simp] theorem toNat_cast (e : w = v) (x : BitVec w) : (cast e x).toNat = x.toNat := rfl

@[simp] theorem getLsb_cast : (cast h x).getLsb i = x.getLsb i := by
  cases h
  simp

/-! ### zeroExtend and truncate -/

@[simp] theorem toNat_zeroExtend' {w v : Nat} (p : w ≤ v) (x : BitVec w) :
    (zeroExtend' p x).toNat = x.toNat := by
  unfold zeroExtend'
  simp [p, x.isLt, Nat.mod_eq_of_lt]

theorem toNat_zeroExtend (v : Nat) (x : BitVec w) :
    BitVec.toNat (zeroExtend v x) = x.toNat % 2^v := by
  let ⟨x, lt_n⟩ := x
  simp only [zeroExtend]
  if n_le_i : w ≤ v then
    have x_lt_two_i : x < 2 ^ v := lt_two_pow_of_le lt_n n_le_i
    simp [n_le_i, Nat.mod_eq_of_lt, x_lt_two_i]
  else
    simp [n_le_i, toNat_ofNat]

@[simp] theorem zeroExtend_eq (x : BitVec w) : zeroExtend w x = x := by
  apply eq_of_toNat_eq
  let ⟨x, lt_n⟩ := x
  simp [truncate, zeroExtend]

@[simp] theorem zeroExtend_zero (w v : Nat) : zeroExtend v (0#w) = 0#v := by
  apply eq_of_toNat_eq
  simp [toNat_zeroExtend]

@[simp] theorem truncate_eq (x : BitVec w) : truncate w x = x := zeroExtend_eq x

@[simp] theorem toNat_truncate (x : BitVec w) : (truncate i x).toNat = x.toNat % 2^i :=
  toNat_zeroExtend i x

@[simp] theorem getLsb_zeroExtend' (ge : v ≥ w) (x : BitVec w) (i : Nat) :
    getLsb (zeroExtend' ge x) i = getLsb x i := by
  simp [getLsb, toNat_zeroExtend']

@[simp] theorem getLsb_zeroExtend (v : Nat) (x : BitVec w) (i : Nat) :
    getLsb (zeroExtend v x) i = (decide (i < v) && getLsb x i) := by
  simp [getLsb, toNat_zeroExtend, Nat.testBit_mod_two_pow]

@[simp] theorem getLsb_truncate (m : Nat) (x : BitVec w) (i : Nat) :
    getLsb (truncate m x) i = (decide (i < m) && getLsb x i) :=
  getLsb_zeroExtend m x i

/-! ## extractLsb -/

@[simp]
protected theorem extractLsb_ofFin (x : Fin (2^w)) (hi lo : Nat) :
  extractLsb hi lo (BitVec.ofFin x) = .ofNat (hi-lo+1) (x.val >>> lo) := rfl

@[simp]
protected theorem extractLsb_ofNat (x w : Nat) (hi lo : Nat) :
    extractLsb hi lo x#w = .ofNat (hi - lo + 1) ((x % 2^w) >>> lo) := by
  apply eq_of_getLsb_eq
  intro ⟨i, _lt⟩
  simp [BitVec.ofNat]

@[simp] theorem extractLsb'_toNat (s v : Nat) (x : BitVec w) :
  (extractLsb' s v x).toNat = (x.toNat >>> s) % 2^v := rfl

@[simp] theorem extractLsb_toNat (hi lo : Nat) (x : BitVec w) :
  (extractLsb hi lo x).toNat = (x.toNat >>> lo) % 2^(hi-lo+1) := rfl

@[simp] theorem getLsb_extract (hi lo : Nat) (x : BitVec w) (i : Nat) :
    getLsb (extractLsb hi lo x) i = (i ≤ (hi-lo) && getLsb x (lo+i)) := by
  unfold getLsb
  simp [Nat.lt_succ]

/-! ### allOnes -/

private theorem allOnes_def :
    allOnes w = .ofFin (⟨0, Nat.two_pow_pos w⟩ - ⟨1 % 2^w, Nat.mod_lt _ (Nat.two_pow_pos w)⟩) := by
  rfl

@[simp] theorem toNat_allOnes : (allOnes w).toNat = 2^w - 1 := by
  simp only [allOnes_def, toNat_ofFin, Fin.coe_sub, Nat.zero_add]
  by_cases h : w = 0
  · subst h
    rfl
  · rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow h), Nat.mod_eq_of_lt]
    exact Nat.pred_lt_self (Nat.two_pow_pos w)

@[simp] theorem getLsb_allOnes : (allOnes w).getLsb i = decide (i < w) := by
  simp only [allOnes_def, getLsb_ofFin, Fin.coe_sub, Nat.zero_add, Nat.testBit_mod_two_pow]
  if h : i < w then
    simp only [h, decide_True, Bool.true_and]
    match i, w, h with
    | i, (w + 1), h =>
      rw [Nat.mod_eq_of_lt (by simp), Nat.testBit_two_pow_sub_one]
      simp [h]
  else
    simp [h]

/-! ### or -/

@[simp] theorem toNat_or (x y : BitVec w) :
    BitVec.toNat (x ||| y) = BitVec.toNat x ||| BitVec.toNat y := rfl

@[simp] theorem toFin_or (x y : BitVec w) :
    BitVec.toFin (x ||| y) = BitVec.toFin x ||| BitVec.toFin y := by
  simp only [HOr.hOr, OrOp.or, BitVec.or, Fin.lor, val_toFin, Fin.mk.injEq]
  exact (Nat.mod_eq_of_lt <| Nat.or_lt_two_pow x.isLt y.isLt).symm

@[simp] theorem getLsb_or {x y : BitVec w} : (x ||| y).getLsb i = (x.getLsb i || y.getLsb i) := by
  rw [← testBit_toNat, getLsb, getLsb]
  simp

/-! ### and -/

@[simp] theorem toNat_and (x y : BitVec w) :
    BitVec.toNat (x &&& y) = BitVec.toNat x &&& BitVec.toNat y := rfl

@[simp] theorem toFin_and (x y : BitVec w) :
    BitVec.toFin (x &&& y) = BitVec.toFin x &&& BitVec.toFin y := by
  simp only [HAnd.hAnd, AndOp.and, BitVec.and, Fin.land, val_toFin, Fin.mk.injEq]
  exact (Nat.mod_eq_of_lt <| Nat.and_lt_two_pow _ y.isLt).symm

@[simp] theorem getLsb_and {x y : BitVec w} : (x &&& y).getLsb i = (x.getLsb i && y.getLsb i) := by
  rw [← testBit_toNat, getLsb, getLsb]
  simp

/-! ### xor -/

@[simp] theorem toNat_xor (x y : BitVec w) :
    BitVec.toNat (x ^^^ y) = BitVec.toNat x ^^^ BitVec.toNat y := rfl

@[simp] theorem toFin_xor (x y : BitVec w) :
    BitVec.toFin (x ^^^ y) = BitVec.toFin x ^^^ BitVec.toFin y := by
  simp only [HXor.hXor, Xor.xor, BitVec.xor, Fin.xor, val_toFin, Fin.mk.injEq]
  exact (Nat.mod_eq_of_lt <| Nat.xor_lt_two_pow x.isLt y.isLt).symm

@[simp] theorem getLsb_xor {x y : BitVec w} :
    (x ^^^ y).getLsb i = (xor (x.getLsb i) (y.getLsb i)) := by
  rw [← testBit_toNat, getLsb, getLsb]
  simp

/-! ### not -/

theorem not_def {x : BitVec w} : ~~~x = allOnes w ^^^ x := rfl

@[simp] theorem toNat_not {x : BitVec w} : (~~~x).toNat = 2^w - 1 - x.toNat := by
  rw [Nat.sub_sub, Nat.add_comm, not_def, toNat_xor]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [toNat_allOnes, Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  match h : BitVec.toNat x with
  | 0 => simp
  | y+1 =>
    rw [Nat.succ_eq_add_one] at h
    rw [← h]
    rw [Nat.testBit_two_pow_sub_succ (toNat_lt _)]
    · cases h_lt : decide (i < w)
      · simp at h_lt
        simp [h_lt]
        rw [Nat.testBit_lt_two_pow]
        calc BitVec.toNat x < 2 ^ w := toNat_lt _
          _ ≤ 2 ^ i := Nat.pow_le_pow_of_le_right Nat.zero_lt_two h_lt
      · simp

@[simp] theorem getLsb_not {x : BitVec w} : (~~~x).getLsb i = (decide (i < w) && ! x.getLsb i) := by
  by_cases h' : i < w <;> simp_all [not_def]

/-! ### shiftLeft -/

@[simp] theorem toNat_shiftLeft {x : BitVec w} :
    BitVec.toNat (x <<< n) = BitVec.toNat x <<< n % 2^w :=
  BitVec.toNat_ofNat _ _

@[simp] theorem getLsb_shiftLeft (x : BitVec w) (n) :
    getLsb (x <<< n) i = (decide (i < w) && !decide (i < n) && getLsb x (i - n)) := by
  rw [← testBit_toNat, getLsb]
  simp only [toNat_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, ge_iff_le]
  -- This step could be a case bashing tactic.
  cases h₁ : decide (i < w) <;> cases h₂ : decide (n ≤ i) <;> cases h₃ : decide (i < n)
  all_goals { simp_all <;> omega }

theorem shiftLeftZeroExtend_eq {x : BitVec w} :
    shiftLeftZeroExtend x n = zeroExtend (w+n) x <<< n := by
  apply eq_of_toNat_eq
  rw [shiftLeftZeroExtend, zeroExtend]
  split
  · simp
    rw [Nat.mod_eq_of_lt]
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right (BitVec.toNat_lt x) (Nat.two_pow_pos _)
  · omega

@[simp] theorem getLsb_shiftLeftZeroExtend (x : BitVec m) (n : Nat) :
    getLsb (shiftLeftZeroExtend x n) i = ((! decide (i < n)) && getLsb x (i - n)) := by
  rw [shiftLeftZeroExtend_eq]
  simp only [getLsb_shiftLeft, getLsb_zeroExtend]
  cases h₁ : decide (i < n) <;> cases h₂ : decide (i - n < m + n) <;> cases h₃ : decide (i < m + n)
    <;> simp_all
    <;> (rw [getLsb_ge]; omega)

/-! ### ushiftRight -/

@[simp] theorem toNat_ushiftRight (x : BitVec w) (i : Nat) :
    (x >>> i).toNat = x.toNat >>> i := rfl

@[simp] theorem getLsb_ushiftRight (x : BitVec w) (i j : Nat) :
    getLsb (x >>> i) j = getLsb x (i+j) := by
  unfold getLsb ; simp

/-! ### append -/

theorem append_def (x : BitVec v) (y : BitVec w) :
    x ++ y = (shiftLeftZeroExtend x w ||| zeroExtend' (Nat.le_add_left w v) y) := rfl

@[simp] theorem toNat_append (x : BitVec v) (y : BitVec w) :
    (x ++ y).toNat = x.toNat <<< w ||| y.toNat :=
  rfl

@[simp] theorem getLsb_append {v : BitVec w} {w : BitVec m} :
    getLsb (v ++ w) i = bif i < m then getLsb w i else getLsb v (i - m) := by
  simp [append_def]
  by_cases h : i < m
  · simp [h]
  · simp [h]; simp_all

/-! ### rev -/

theorem getLsb_rev (x : BitVec w) (i : Fin w) :
    x.getLsb i.rev = x.getMsb i := by
  simp [getLsb, getMsb]
  congr 1
  omega

theorem getMsb_rev (x : BitVec w) (i : Fin w) :
    x.getMsb i.rev = x.getLsb i := by
  simp only [← getLsb_rev]
  simp only [Fin.rev]
  congr
  omega

/-! ### cons -/

@[simp] theorem toNat_cons (b : Bool) (x : BitVec w) :
    (cons b x).toNat = (b.toNat <<< w) ||| x.toNat := by
  let ⟨x, _⟩ := x
  simp [cons, toNat_append, toNat_ofBool]

@[simp] theorem getLsb_cons (b : Bool) (x : BitVec w) (i : Nat) :
    getLsb (cons b x) i = if i = w then b else getLsb x i := by
  simp only [getLsb, toNat_cons, Nat.testBit_or]
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_trichotomy i w with i_lt_n | i_eq_n | n_lt_i
  · have p1 : ¬(w ≤ i) := by omega
    have p2 : i ≠ w := by omega
    simp [p1, p2]
  · simp [i_eq_n, testBit_toNat]
    cases b <;> trivial
  · have p1 : i ≠ w := by omega
    have p2 : i - w ≠ 0 := by omega
    simp [p1, p2, Nat.testBit_bool_to_nat]

theorem truncate_succ (x : BitVec w) :
    truncate (i+1) x = cons (getLsb x i) (truncate i x) := by
  apply eq_of_getLsb_eq
  intro j
  simp only [getLsb_truncate, getLsb_cons, j.isLt, decide_True, Bool.true_and]
  if j_eq : j.val = i then
    simp [j_eq]
  else
    have j_lt : j.val < i := Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ j.isLt) j_eq
    simp [j_eq, j_lt]

/-! ### add -/

theorem add_def (x y : BitVec w) : x + y = .ofNat w (x.toNat + y.toNat) := rfl

/--
Definition of bitvector addition as a nat.
-/
@[simp] theorem toNat_add (x y : BitVec w) : (x + y).toNat = (x.toNat + y.toNat) % 2^w := rfl
@[simp] theorem toFin_add (x y : BitVec w) : (x + y).toFin = toFin x + toFin y := rfl
@[simp] theorem ofFin_add (x : Fin (2^w)) (y : BitVec w) :
  .ofFin x + y = .ofFin (x + y.toFin) := rfl
@[simp] theorem add_ofFin (x : BitVec w) (y : Fin (2^w)) :
  x + .ofFin y = .ofFin (x.toFin + y) := rfl
@[simp] theorem ofNat_add_ofNat {n} (x y : Nat) : x#n + y#n = (x + y)#n := by
  apply eq_of_toNat_eq ; simp [BitVec.ofNat]

protected theorem add_assoc (x y z : BitVec w) : x + y + z = x + (y + z) := by
  apply eq_of_toNat_eq ; simp [Nat.add_assoc]

protected theorem add_comm (x y : BitVec w) : x + y = y + x := by
  simp [add_def, Nat.add_comm]

@[simp] protected theorem add_zero (x : BitVec w) : x + 0#w = x := by simp [add_def]

@[simp] protected theorem zero_add (x : BitVec w) : 0#w + x = x := by simp [add_def]


/-! ### sub/neg -/

theorem sub_def (x y : BitVec w) : x - y = .ofNat w (x.toNat + (2^w - y.toNat)) := by rfl

@[simp] theorem toNat_sub (x y : BitVec w) :
  (x - y).toNat = ((x.toNat + (2^w - y.toNat)) % 2^w) := rfl
@[simp] theorem toFin_sub (x y : BitVec n) : (x - y).toFin = toFin x - toFin y := rfl

/-- Replaced 2024-02-06. -/
@[deprecated] alias sub_toNat := toNat_sub

@[simp] theorem ofFin_sub (x : Fin (2^w)) (y : BitVec w) : .ofFin x - y = .ofFin (x - y.toFin) :=
  rfl
@[simp] theorem sub_ofFin (x : BitVec w) (y : Fin (2^w)) : x - .ofFin y = .ofFin (x.toFin - y) :=
  rfl
@[simp] theorem ofNat_sub_ofNat (x y : Nat) : x#w - y#w = .ofNat w (x + (2^w - y % 2^w)) := by
  apply eq_of_toNat_eq ; simp [BitVec.ofNat]

@[simp] protected theorem sub_zero (x : BitVec w) : x - (0#w) = x := by apply eq_of_toNat_eq ; simp

@[simp] protected theorem sub_self (x : BitVec w) : x - x = 0#w := by
  apply eq_of_toNat_eq
  simp only [toNat_sub]
  rw [Nat.add_sub_of_le]
  · simp
  · exact Nat.le_of_lt x.isLt

@[simp] theorem toNat_neg (x : BitVec w) : (- x).toNat = (2^w - x.toNat) % 2^w := by
  simp [Neg.neg, BitVec.neg]

/-- Replaced 2024-02-06. -/
@[deprecated] alias neg_toNat := toNat_neg

theorem sub_toAdd (x y : BitVec w) : x - y = x + - y := by
  apply eq_of_toNat_eq
  simp

@[simp] theorem neg_zero (n:Nat) : -0#n = 0#n := by apply eq_of_toNat_eq ; simp

theorem add_sub_cancel (x y : BitVec w) : x + y - y = x := by
  apply eq_of_toNat_eq
  have y_toNat_le := Nat.le_of_lt y.toNat_lt
  rw [toNat_sub, toNat_add, Nat.mod_add_mod, Nat.add_assoc, ← Nat.add_sub_assoc y_toNat_le,
    Nat.add_sub_cancel_left, Nat.add_mod_right, toNat_mod_cancel]

/-! ### mul -/

theorem mul_def {x y : BitVec w} : x * y = (ofFin <| x.toFin * y.toFin) := by rfl

theorem toNat_mul (x y : BitVec n) : (x * y).toNat = (x.toNat * y.toNat) % 2 ^ n := rfl
@[simp] theorem toFin_mul (x y : BitVec n) : (x * y).toFin = (x.toFin * y.toFin) := rfl

/-! ### le and lt -/

theorem le_def (x y : BitVec w) :
  x ≤ y ↔ x.toNat ≤ y.toNat := Iff.rfl

@[simp] theorem le_ofFin (x : BitVec w) (y : Fin (2^w)) :
  x ≤ BitVec.ofFin y ↔ x.toFin ≤ y := Iff.rfl
@[simp] theorem ofFin_le (x : Fin (2^w)) (y : BitVec w) :
  BitVec.ofFin x ≤ y ↔ x ≤ y.toFin := Iff.rfl
@[simp] theorem ofNat_le_ofNat (x y : Nat) : (x#w) ≤ (y#w) ↔ x % 2^w ≤ y % 2^w := by
  simp [le_def]

theorem lt_def (x y : BitVec w) :
  x < y ↔ x.toNat < y.toNat := Iff.rfl

@[simp] theorem lt_ofFin (x : BitVec w) (y : Fin (2^w)) :
  x < BitVec.ofFin y ↔ x.toFin < y := Iff.rfl
@[simp] theorem ofFin_lt (x : Fin (2^w)) (y : BitVec w) :
  BitVec.ofFin x < y ↔ x < y.toFin := Iff.rfl
@[simp] theorem ofNat_lt_ofNat (x y : Nat) : (x#w) < (y#w) ↔ x % 2^w < y % 2^w := by
  simp [lt_def]

protected theorem lt_of_le_ne (x y : BitVec w) (h1 : x <= y) (h2 : ¬ x = y) : x < y := by
  revert h1 h2
  let ⟨x, lt⟩ := x
  let ⟨y, lt⟩ := y
  simp
  exact Nat.lt_of_le_of_ne
