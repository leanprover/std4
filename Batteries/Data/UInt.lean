/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais, Mario Carneiro
-/
import Batteries.Classes.Order

/-! ### UInt8 -/

@[ext] theorem UInt8.ext : {x y : UInt8} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem UInt8.ext_iff {x y : UInt8} : x = y ↔ x.toNat = y.toNat := ⟨congrArg _, UInt8.ext⟩

@[simp] theorem UInt8.val_val_eq_toNat (x : UInt8) : x.val.val = x.toNat := rfl

@[simp] theorem UInt8.val_ofNat (n) :
    (no_index (OfNat.ofNat n) : UInt8).val = OfNat.ofNat n := rfl

@[simp] theorem UInt8.toNat_ofNat (n) :
    (no_index (OfNat.ofNat n) : UInt8).toNat = n % UInt8.size := rfl

theorem UInt8.toNat_lt (x : UInt8) : x.toNat < 2 ^ 8 := x.val.isLt

@[simp] theorem UInt8.toUInt16_toNat (x : UInt8) : x.toUInt16.toNat = x.toNat := rfl

@[simp] theorem UInt8.toUInt32_toNat (x : UInt8) : x.toUInt32.toNat = x.toNat := rfl

@[simp] theorem UInt8.toUInt64_toNat (x : UInt8) : x.toUInt64.toNat = x.toNat := rfl

theorem UInt8.toNat_zero : (0 : UInt8).toNat = 0 := rfl

theorem UInt8.toNat_add (x y : UInt8) : (x + y).toNat = (x.toNat + y.toNat) % UInt8.size := rfl

theorem UInt8.toNat_sub (x y : UInt8) :
    (x - y).toNat = (UInt8.size - y.toNat + x.toNat) % UInt8.size := rfl

theorem UInt8.toNat_mul (x y : UInt8) : (x * y).toNat = (x.toNat * y.toNat) % UInt8.size := rfl

theorem UInt8.toNat_div (x y : UInt8) : (x / y).toNat = x.toNat / y.toNat := rfl

theorem UInt8.toNat_mod (x y : UInt8) : (x % y).toNat = x.toNat % y.toNat := rfl

theorem UInt8.toNat_modn (x : UInt8) (n) : (x.modn n).toNat = x.toNat % n := rfl

/-- Maximum `UInt8` value. -/
def UInt8.last : UInt8 := ⟨UInt8.size.pred, Nat.pred_lt (by decide)⟩

@[simp] theorem UInt8.last_toNat : UInt8.last.toNat = UInt8.size - 1 := rfl

@[simp] theorem UInt8.zero_le (x : UInt8) : 0 ≤ x := Nat.zero_le _

@[simp] theorem UInt8.le_last (x : UInt8) : x ≤ last := Nat.le_of_lt_succ <| UInt8.toNat_lt _

theorem UInt8.le_antisymm_iff {x y : UInt8} : x = y ↔ x ≤ y ∧ y ≤ x :=
  UInt8.ext_iff.trans Nat.le_antisymm_iff

theorem UInt8.le_antisymm {x y : UInt8} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  UInt8.le_antisymm_iff.2 ⟨h1, h2⟩

instance : Batteries.LawfulOrd UInt8 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt8.le_antisymm

theorem UInt8.le_iff_toNat_le_toNat {x y : UInt8} : x ≤ y ↔ x.toNat ≤ y.toNat := .rfl

theorem UInt8.lt_iff_toNat_lt_toNat {x y : UInt8} : x < y ↔ x.toNat < y.toNat := .rfl

theorem UInt8.compare_eq_toNat_compare_toNat (x y : UInt8) :
    compare x y = compare x.toNat y.toNat := by
  simp only [compare, compareOfLessAndEq, lt_iff_toNat_lt_toNat, ext_iff]

theorem UInt8.max_def (x y : UInt8) : max x y = if x ≤ y then y else x := rfl

theorem UInt8.min_def (x y : UInt8) : min x y = if x ≤ y then x else y := rfl

theorem UInt8.toNat_max (x y : UInt8) : (max x y).toNat = max x.toNat y.toNat := by
  rw [max_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_right h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_left (Nat.le_of_not_ge h)]

theorem UInt8.toNat_min (x y : UInt8) : (min x y).toNat = min x.toNat y.toNat := by
  rw [min_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_left h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_right (Nat.le_of_not_ge h)]

/-! ### UInt16 -/

@[ext] theorem UInt16.ext : {x y : UInt16} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem UInt16.ext_iff {x y : UInt16} : x = y ↔ x.toNat = y.toNat := ⟨congrArg _, UInt16.ext⟩

@[simp] theorem UInt16.val_val_eq_toNat (x : UInt16) : x.val.val = x.toNat := rfl

@[simp] theorem UInt16.val_ofNat (n) :
    (no_index (OfNat.ofNat n) : UInt16).val = OfNat.ofNat n := rfl

@[simp] theorem UInt16.toNat_ofNat (n) :
    (no_index (OfNat.ofNat n) : UInt16).toNat = n % UInt16.size := rfl

theorem UInt16.toNat_lt (x : UInt16) : x.toNat < 2 ^ 16 := x.val.isLt

@[simp] theorem UInt16.toUInt8_toNat (x : UInt16) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt16.toUInt32_toNat (x : UInt16) : x.toUInt32.toNat = x.toNat := rfl

@[simp] theorem UInt16.toUInt64_toNat (x : UInt16) : x.toUInt64.toNat = x.toNat := rfl

theorem UInt16.toNat_zero : (0 : UInt16).toNat = 0 := rfl

theorem UInt16.toNat_add (x y : UInt16) : (x + y).toNat = (x.toNat + y.toNat) % UInt16.size := rfl

theorem UInt16.toNat_sub (x y : UInt16) :
    (x - y).toNat = (UInt16.size - y.toNat + x.toNat) % UInt16.size := rfl

theorem UInt16.toNat_mul (x y : UInt16) : (x * y).toNat = (x.toNat * y.toNat) % UInt16.size := rfl

theorem UInt16.toNat_div (x y : UInt16) : (x / y).toNat = x.toNat / y.toNat := rfl

theorem UInt16.toNat_mod (x y : UInt16) : (x % y).toNat = x.toNat % y.toNat := rfl

theorem UInt16.toNat_modn (x : UInt16) (n) : (x.modn n).toNat = x.toNat % n := rfl

/-- Maximum `UInt16` value. -/
def UInt16.last : UInt16 := ⟨UInt16.size.pred, Nat.pred_lt (by decide)⟩

@[simp] theorem UInt16.last_toNat : UInt16.last.toNat = UInt16.size - 1 := rfl

@[simp] theorem UInt16.zero_le (x : UInt16) : 0 ≤ x := Nat.zero_le _

@[simp] theorem UInt16.le_last (x : UInt16) : x ≤ last := Nat.le_of_lt_succ <| UInt16.toNat_lt _

theorem UInt16.le_antisymm_iff {x y : UInt16} : x = y ↔ x ≤ y ∧ y ≤ x :=
  UInt16.ext_iff.trans Nat.le_antisymm_iff

theorem UInt16.le_antisymm {x y : UInt16} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  UInt16.le_antisymm_iff.2 ⟨h1, h2⟩

instance : Batteries.LawfulOrd UInt16 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt16.le_antisymm

theorem UInt16.le_iff_toNat_le_toNat {x y : UInt16} : x ≤ y ↔ x.toNat ≤ y.toNat := .rfl

theorem UInt16.lt_iff_toNat_lt_toNat {x y : UInt16} : x < y ↔ x.toNat < y.toNat := .rfl

theorem UInt16.compare_eq_toNat_compare_toNat (x y : UInt16) :
    compare x y = compare x.toNat y.toNat := by
  simp only [compare, compareOfLessAndEq, lt_iff_toNat_lt_toNat, ext_iff]

theorem UInt16.max_def (x y : UInt16) : max x y = if x ≤ y then y else x := rfl

theorem UInt16.min_def (x y : UInt16) : min x y = if x ≤ y then x else y := rfl

theorem UInt16.toNat_max (x y : UInt16) : (max x y).toNat = max x.toNat y.toNat := by
  rw [max_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_right h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_left (Nat.le_of_not_ge h)]

theorem UInt16.toNat_min (x y : UInt16) : (min x y).toNat = min x.toNat y.toNat := by
  rw [min_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_left h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_right (Nat.le_of_not_ge h)]

/-! ### UInt32 -/

@[ext] theorem UInt32.ext : {x y : UInt32} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem UInt32.ext_iff {x y : UInt32} : x = y ↔ x.toNat = y.toNat := ⟨congrArg _, UInt32.ext⟩

@[simp] theorem UInt32.val_val_eq_toNat (x : UInt32) : x.val.val = x.toNat := rfl

@[simp] theorem UInt32.val_ofNat (n) :
    (no_index (OfNat.ofNat n) : UInt32).val = OfNat.ofNat n := rfl

@[simp] theorem UInt32.toNat_ofNat (n) :
    (no_index (OfNat.ofNat n) : UInt32).toNat = n % UInt32.size := rfl

theorem UInt32.toNat_lt (x : UInt32) : x.toNat < 2 ^ 32 := x.val.isLt

@[simp] theorem UInt32.toUInt8_toNat (x : UInt32) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt32.toUInt16_toNat (x : UInt32) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl

@[simp] theorem UInt32.toUInt64_toNat (x : UInt32) : x.toUInt64.toNat = x.toNat := rfl

theorem UInt32.toNat_zero : (0 : UInt32).toNat = 0 := rfl

theorem UInt32.toNat_add (x y : UInt32) : (x + y).toNat = (x.toNat + y.toNat) % UInt32.size := rfl

theorem UInt32.toNat_sub (x y : UInt32) :
    (x - y).toNat = (UInt32.size - y.toNat + x.toNat) % UInt32.size := rfl

theorem UInt32.toNat_mul (x y : UInt32) : (x * y).toNat = (x.toNat * y.toNat) % UInt32.size := rfl

theorem UInt32.toNat_div (x y : UInt32) : (x / y).toNat = x.toNat / y.toNat := rfl

theorem UInt32.toNat_mod (x y : UInt32) : (x % y).toNat = x.toNat % y.toNat := rfl

theorem UInt32.toNat_modn (x : UInt32) (n) : (x.modn n).toNat = x.toNat % n := rfl

/-- Maximum `UInt32` value. -/
def UInt32.last : UInt32 := ⟨UInt32.size.pred, Nat.pred_lt (by decide)⟩

@[simp] theorem UInt32.last_toNat : UInt32.last.toNat = UInt32.size - 1 := rfl

@[simp] theorem UInt32.zero_le (x : UInt32) : 0 ≤ x := Nat.zero_le _

@[simp] theorem UInt32.le_last (x : UInt32) : x ≤ last := Nat.le_of_lt_succ <| UInt32.toNat_lt _

theorem UInt32.le_antisymm_iff {x y : UInt32} : x = y ↔ x ≤ y ∧ y ≤ x :=
  UInt32.ext_iff.trans Nat.le_antisymm_iff

theorem UInt32.le_antisymm {x y : UInt32} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  UInt32.le_antisymm_iff.2 ⟨h1, h2⟩

instance : Batteries.LawfulOrd UInt32 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt32.le_antisymm

theorem UInt32.le_iff_toNat_le_toNat {x y : UInt32} : x ≤ y ↔ x.toNat ≤ y.toNat := .rfl

theorem UInt32.lt_iff_toNat_lt_toNat {x y : UInt32} : x < y ↔ x.toNat < y.toNat := .rfl

theorem UInt32.compare_eq_toNat_compare_toNat (x y : UInt32) :
    compare x y = compare x.toNat y.toNat := by
  simp only [compare, compareOfLessAndEq, lt_iff_toNat_lt_toNat, ext_iff]

theorem UInt32.max_def (x y : UInt32) : max x y = if x ≤ y then y else x := rfl

theorem UInt32.min_def (x y : UInt32) : min x y = if x ≤ y then x else y := rfl

theorem UInt32.toNat_max (x y : UInt32) : (max x y).toNat = max x.toNat y.toNat := by
  rw [max_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_right h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_left (Nat.le_of_not_ge h)]

theorem UInt32.toNat_min (x y : UInt32) : (min x y).toNat = min x.toNat y.toNat := by
  rw [min_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_left h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_right (Nat.le_of_not_ge h)]

/-! ### UInt64 -/

@[ext] theorem UInt64.ext : {x y : UInt64} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem UInt64.ext_iff {x y : UInt64} : x = y ↔ x.toNat = y.toNat := ⟨congrArg _, UInt64.ext⟩

@[simp] theorem UInt64.val_val_eq_toNat (x : UInt64) : x.val.val = x.toNat := rfl

@[simp] theorem UInt64.val_ofNat (n) :
    (no_index (OfNat.ofNat n) : UInt64).val = OfNat.ofNat n := rfl

@[simp] theorem UInt64.toNat_ofNat (n) :
    (no_index (OfNat.ofNat n) : UInt64).toNat = n % UInt64.size := rfl

theorem UInt64.toNat_lt (x : UInt64) : x.toNat < 2 ^ 64 := x.val.isLt

@[simp] theorem UInt64.toUInt8_toNat (x : UInt64) : x.toUInt8.toNat = x.toNat % 2 ^ 8 := rfl

@[simp] theorem UInt64.toUInt16_toNat (x : UInt64) : x.toUInt16.toNat = x.toNat % 2 ^ 16 := rfl

@[simp] theorem UInt64.toUInt32_toNat (x : UInt64) : x.toUInt32.toNat = x.toNat % 2 ^ 32 := rfl

theorem UInt64.toNat_zero : (0 : UInt64).toNat = 0 := rfl

theorem UInt64.toNat_add (x y : UInt64) : (x + y).toNat = (x.toNat + y.toNat) % UInt64.size := rfl

theorem UInt64.toNat_sub (x y : UInt64) :
    (x - y).toNat = (UInt64.size - y.toNat + x.toNat) % UInt64.size := rfl

theorem UInt64.toNat_mul (x y : UInt64) : (x * y).toNat = (x.toNat * y.toNat) % UInt64.size := rfl

theorem UInt64.toNat_div (x y : UInt64) : (x / y).toNat = x.toNat / y.toNat := rfl

theorem UInt64.toNat_mod (x y : UInt64) : (x % y).toNat = x.toNat % y.toNat := rfl

theorem UInt64.toNat_modn (x : UInt64) (n) : (x.modn n).toNat = x.toNat % n := rfl

/-- Maximum `UInt64` value. -/
def UInt64.last : UInt64 := ⟨UInt64.size.pred, Nat.pred_lt (by decide)⟩

@[simp] theorem UInt64.last_toNat : UInt64.last.toNat = UInt64.size - 1 := rfl

@[simp] theorem UInt64.zero_le (x : UInt64) : 0 ≤ x := Nat.zero_le _

@[simp] theorem UInt64.le_last (x : UInt64) : x ≤ last := Nat.le_of_lt_succ <| UInt64.toNat_lt _


theorem UInt64.le_antisymm_iff {x y : UInt64} : x = y ↔ x ≤ y ∧ y ≤ x :=
  UInt64.ext_iff.trans Nat.le_antisymm_iff

theorem UInt64.le_antisymm {x y : UInt64} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  UInt64.le_antisymm_iff.2 ⟨h1, h2⟩

instance : Batteries.LawfulOrd UInt64 := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt UInt64.le_antisymm

theorem UInt64.le_iff_toNat_le_toNat {x y : UInt64} : x ≤ y ↔ x.toNat ≤ y.toNat := .rfl

theorem UInt64.lt_iff_toNat_lt_toNat {x y : UInt64} : x < y ↔ x.toNat < y.toNat := .rfl

theorem UInt64.compare_eq_toNat_compare_toNat (x y : UInt64) :
    compare x y = compare x.toNat y.toNat := by
  simp only [compare, compareOfLessAndEq, lt_iff_toNat_lt_toNat, ext_iff]

theorem UInt64.max_def (x y : UInt64) : max x y = if x ≤ y then y else x := rfl

theorem UInt64.min_def (x y : UInt64) : min x y = if x ≤ y then x else y := rfl

theorem UInt64.toNat_max (x y : UInt64) : (max x y).toNat = max x.toNat y.toNat := by
  rw [max_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_right h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_left (Nat.le_of_not_ge h)]

theorem UInt64.toNat_min (x y : UInt64) : (min x y).toNat = min x.toNat y.toNat := by
  rw [min_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_left h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_right (Nat.le_of_not_ge h)]

/-! ### USize -/

@[ext] theorem USize.ext : {x y : USize} → x.toNat = y.toNat → x = y
  | ⟨⟨_,_⟩⟩, ⟨⟨_,_⟩⟩, rfl => rfl

theorem USize.ext_iff {x y : USize} : x = y ↔ x.toNat = y.toNat := ⟨congrArg _, USize.ext⟩

@[simp] theorem USize.val_val_eq_toNat (x : USize) : x.val.val = x.toNat := rfl

@[simp] theorem USize.val_ofNat (n) :
    (no_index (OfNat.ofNat n) : USize).val = OfNat.ofNat n := rfl

@[simp] theorem USize.toNat_ofNat (n) :
    (no_index (OfNat.ofNat n) : USize).toNat = n % USize.size := rfl

theorem USize.size_eq : USize.size = 2 ^ System.Platform.numBits := by
  have : 1 ≤ 2 ^ System.Platform.numBits := Nat.succ_le_of_lt (Nat.two_pow_pos _)
  rw [USize.size, Nat.sub_add_cancel this]

theorem USize.le_size : 2 ^ 32 ≤ USize.size := by
  rw [size_eq]
  apply Nat.pow_le_pow_of_le_right (by decide)
  cases System.Platform.numBits_eq <;> simp_arith [*]

theorem USize.size_le : USize.size ≤ 2 ^ 64 := by
  rw [size_eq]
  apply Nat.pow_le_pow_of_le_right (by decide)
  cases System.Platform.numBits_eq <;> simp_arith [*]

theorem USize.toNat_lt (x : USize) : x.toNat < USize.size := x.val.isLt

@[simp] theorem USize.toUInt64_toNat (x : USize) : x.toUInt64.toNat = x.toNat := by
  simp only [USize.toUInt64, UInt64.toNat]; rfl

@[simp] theorem UInt32.toUSize_toNat (x : UInt32) : x.toUSize.toNat = x.toNat := rfl

theorem USize.toNat_zero : (0 : USize).toNat = 0 := rfl

theorem USize.toNat_add (x y : USize) : (x + y).toNat = (x.toNat + y.toNat) % USize.size := rfl

theorem USize.toNat_sub (x y : USize) :
    (x - y).toNat = (USize.size - y.toNat + x.toNat) % USize.size := rfl

theorem USize.toNat_mul (x y : USize) : (x * y).toNat = (x.toNat * y.toNat) % USize.size := rfl

theorem USize.toNat_div (x y : USize) : (x / y).toNat = x.toNat / y.toNat := rfl

theorem USize.toNat_mod (x y : USize) : (x % y).toNat = x.toNat % y.toNat := rfl

theorem USize.toNat_modn (x : USize) (n) : (x.modn n).toNat = x.toNat % n := rfl

/-- Maximum `USize` value. -/
def USize.last : USize := ⟨USize.size.pred, Nat.pred_lt (by decide)⟩

@[simp] theorem USize.last_toNat : USize.last.toNat = USize.size - 1 := rfl

@[simp] theorem USize.zero_le (x : USize) : 0 ≤ x := Nat.zero_le _

@[simp] theorem USize.le_last (x : USize) : x ≤ last := Nat.le_of_lt_succ <| (USize.val _).is_lt

theorem USize.le_antisymm_iff {x y : USize} : x = y ↔ x ≤ y ∧ y ≤ x :=
  USize.ext_iff.trans Nat.le_antisymm_iff

theorem USize.le_antisymm {x y : USize} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  USize.le_antisymm_iff.2 ⟨h1, h2⟩

instance : Batteries.LawfulOrd USize := .compareOfLessAndEq
  (fun _ => Nat.lt_irrefl _) Nat.lt_trans Nat.not_lt USize.le_antisymm

theorem USize.le_iff_toNat_le_toNat {x y : USize} : x ≤ y ↔ x.toNat ≤ y.toNat := .rfl

theorem USize.lt_iff_toNat_lt_toNat {x y : USize} : x < y ↔ x.toNat < y.toNat := .rfl

theorem USize.compare_eq_toNat_compare_toNat (x y : USize) :
    compare x y = compare x.toNat y.toNat := by
  simp only [compare, compareOfLessAndEq, lt_iff_toNat_lt_toNat, ext_iff]

theorem USize.max_def (x y : USize) : max x y = if x ≤ y then y else x := rfl

theorem USize.min_def (x y : USize) : min x y = if x ≤ y then x else y := rfl

theorem USize.toNat_max (x y : USize) : (max x y).toNat = max x.toNat y.toNat := by
  rw [max_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_right h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.max_eq_left (Nat.le_of_not_ge h)]

theorem USize.toNat_min (x y : USize) : (min x y).toNat = min x.toNat y.toNat := by
  rw [min_def]
  split
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_left h]
  · next h =>
      rw [le_iff_toNat_le_toNat] at h
      rw [Nat.min_eq_right (Nat.le_of_not_ge h)]
