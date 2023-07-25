/-
Copyright (c) 2023 F. G. Dorais. No rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: F. G. Dorais
-/

import Std.Tactic.Alias

/-- Boolean exclusive or -/
abbrev xor : Bool → Bool → Bool := bne

@[inherit_doc] infixl:30 " ^^ " => xor

namespace Bool
variable (x y z : Bool)

/- Boolean truth table tactic -/
local syntax "btt" (&"using" tactic)? (colGt term:max)* : tactic
macro_rules
| `(tactic| btt) => `(tactic| rfl)
| `(tactic| btt using $tac) => `(tactic| $tac)
| `(tactic| btt $[using $tac]? $x:term $xs:term*) =>
  `(tactic| cases ($x : Bool) <;> btt $[using $tac]? $xs*)

instance : LE Bool := leOfOrd
instance : LT Bool := ltOfOrd
instance : Max Bool := maxOfLe
instance : Min Bool := minOfLe

@[simp] theorem and_not_self_left : (!x && x) = false := by btt x
@[simp] theorem and_not_self_right : (x && !x) = false := by btt x
theorem and_comm : (x && y) = (y && x) := by btt x y
theorem and_left_comm : (x && (y && z)) = (y && (x && z)) := by btt x y z
theorem and_right_comm : ((x && y) && z) = ((x && z) && y) := by btt x y z
theorem and_or_distrib_left : (x && (y || z)) = ((x && y) || (x && z)) := by btt x y z
theorem and_or_distrib_right : ((x || y) && z) = ((x && z) || (y && z)) := by btt x y z
theorem and_xor_distrib_left : (x && (y ^^ z)) = ((x && y) ^^ (x && z)) := by btt x y z
theorem and_xor_distrib_right : ((x ^^ y) && z) = ((x && z) ^^ (y && z)) := by btt x y z
@[local simp] theorem and_deMorgan : (!(x && y)) = (!x || !y) := by btt x y
theorem and_eq_true_iff : (x && y) = true ↔ x = true ∧ y = true := by btt using simp x y
theorem and_eq_false_iff : (x && y) = false ↔ x = false ∨ y = false := by btt using simp x y
alias Bool.false_and ← and_false_left
alias Bool.and_false ← and_false_right
alias Bool.true_and ← and_true_left
alias Bool.and_true ← and_true_right
alias Bool.and_deMorgan ← not_and

@[simp] theorem or_not_self_left : (!x || x) = true := by btt x
@[simp] theorem or_not_self_right : (x || !x) = true := by btt x
theorem or_comm : (x || y) = (y || x) := by btt x y
theorem or_left_comm : (x || (y || z)) = (y || (x || z)) := by btt x y z
theorem or_right_comm : ((x || y) || z) = ((x || z) || y) := by btt x y z
theorem or_and_distrib_left : (x || (y && z)) = ((x || y) && (x || z)) := by btt x y z
theorem or_and_distrib_right : ((x && y) || z) = ((x || z) && (y || z)) := by btt x y z
@[local simp] theorem or_deMorgan : (!(x || y)) = (!x && !y) := by btt x y
theorem or_eq_true_iff : (x || y) = true ↔ x = true ∨ y = true := by btt using simp x y
theorem or_eq_false_iff : (x || y) = false ↔ x = false ∧ y = false := by btt using simp x y
alias Bool.false_or ← or_false_left
alias Bool.or_false ← or_false_right
alias Bool.true_or ← or_true_left
alias Bool.or_true ← or_true_right
alias Bool.or_deMorgan ← not_or

@[simp] theorem false_xor : (false ^^ x) = x := by btt x
@[simp] theorem true_xor : (true ^^ x) = !x := by btt x
@[simp] theorem xor_false : (x ^^ false) = x := by btt x
@[simp] theorem xor_true : (x ^^ true) = !x := by btt x
@[simp] theorem xor_not_self_left : (!x ^^ x) = true := by btt x
@[simp] theorem xor_not_self_right : (x ^^ !x) = true := by btt x
@[simp] theorem xor_self : (x ^^ x) = false := bne_self_eq_false ..
theorem xor_comm : (x ^^ y) = (y ^^ x) := by btt x y
theorem xor_left_comm : (x ^^ (y ^^ z)) = (y ^^ (x ^^ z)) := by btt x y z
theorem xor_right_comm : ((x ^^ y) ^^ z) = ((x ^^ z) ^^ y) := by btt x y z
theorem xor_assoc : ((x ^^ y) ^^ z) = (x ^^ (y ^^ z)) := by btt x y z
alias Bool.false_xor ← xor_false_left
alias Bool.xor_false ← xor_false_right
alias Bool.true_xor ← xor_true_left
alias Bool.xor_true ← xor_true_right

@[simp] protected theorem le_refl : x ≤ x := by btt x
@[simp] protected theorem lt_irrefl : ¬ x < x := by btt using simp x
protected theorem le_trans {x y z : Bool} : x ≤ y → y ≤ z → x ≤ z := by btt using simp x y z
protected theorem le_antisymm {x y : Bool} : x ≤ y → y ≤ x → x = y := by btt using simp x y
protected theorem le_total (x y : Bool) : x ≤ y ∨ y ≤ x := by btt using simp x y
protected theorem lt_asymm {x y : Bool} : x < y → ¬ y < x := by btt using simp x y
protected theorem lt_trans {x y z : Bool} : x < y → y < z → x < z := by btt using simp x y z
protected theorem lt_iff_le_not_le {x y : Bool} : x < y ↔ x ≤ y ∧ ¬ y ≤ x := by btt using simp x y
protected theorem lt_of_le_of_lt {x y z : Bool} : x ≤ y → y < z → x < z := by btt using simp x y z
protected theorem lt_of_lt_of_le {x y z : Bool} : x < y → y ≤ z → x < z := by btt using simp x y z
protected theorem le_of_lt {x y : Bool} : x < y → x ≤ y := by btt using simp x y z
protected theorem le_of_eq {x y : Bool} : x = y → x ≤ y := by btt using simp x y z
protected theorem ne_of_lt {x y : Bool} : x < y → x ≠ y := by btt using simp x y z
protected theorem lt_of_le_of_ne {x y : Bool} : x ≤ y → x ≠ y → x < y := by btt using simp x y z
protected theorem le_of_lt_or_eq {x y : Bool} : x < y ∨ x = y → x ≤ y := by btt using simp x y z
@[simp] protected theorem le_true : x ≤ true := by btt x
@[simp] protected theorem false_le : false ≤ x := by btt x
protected theorem eq_true_of_true_le {x : Bool} : true ≤ x → x = true := by btt using simp x
protected theorem eq_false_of_le_false {x : Bool} : x ≤ false → x = false := by btt using simp x

protected theorem max_eq_or (x y : Bool) : max x y = (x || y) := by btt using simp x y
protected theorem min_eq_and (x y : Bool) : min x y = (x && y) := by btt using simp x y

theorem not_inj {x y : Bool} : (!x) = (!y) → x = y := by btt using simp x y

theorem not_inj' {x y : Bool} : (!x) = (!y) ↔ x = y := ⟨not_inj, fun | rfl => rfl⟩

theorem and_or_inj_right {m x y : Bool}: (x && m) = (y && m) → (x || m) = (y || m) → x = y := by
  btt using simp m x y

theorem and_or_inj_right' {m x y : Bool}: (x && m) = (y && m) ∧ (x || m) = (y || m) ↔ x = y :=
  ⟨fun ⟨h₁, h₂⟩ => and_or_inj_right h₁ h₂, fun | rfl => ⟨rfl, rfl⟩⟩

theorem and_or_inj_left {m x y : Bool} : (m && x) = (m && y) → (m || x) = (m || y) → x = y := by
  btt using simp m x y

theorem and_or_inj_left' {m x y : Bool} : (m && x) = (m && y) ∧ (m || x) = (m || y) ↔ x = y :=
  ⟨fun ⟨h₁, h₂⟩ => and_or_inj_left h₁ h₂, fun | rfl => ⟨rfl, rfl⟩⟩

section
variable (xs ys : List Bool)

attribute [local simp] and_assoc or_assoc xor_assoc List.map List.join

/-- Boolean conjunction (`and`) of a list -/
abbrev all : Bool := xs.all id

@[simp] theorem all_nil : all [] = true := rfl

@[local simp] theorem all_cons  : all (x :: xs) = (x && all xs) := rfl

theorem all_one : all [x] = x := by simp

theorem all_two : all [x, y] = (x && y) := by simp

@[local simp] theorem all_append : all (xs ++ ys) = (all xs && all ys) := by
  induction xs with | nil => rfl | cons _ _ ih => simp [ih]

theorem all_join (xss : List (List Bool)) : all (xss.map all) = all xss.join := by
  induction xss with | nil => rfl | cons _ _ ih => simp [ih]

/-- Boolean disjunction (`or`) of a list -/
abbrev any : Bool := xs.any id

@[simp] theorem any_nil : any [] = false := rfl

@[local simp] theorem any_cons : any (x :: xs) = (x || any xs) := rfl

theorem any_one : any [x] = x := by simp

theorem any_two : any [x, y] = (x || y) := by simp

@[local simp] theorem any_append : any (xs ++ ys) = (any xs || any ys) := by
  induction xs with | nil => rfl | cons _ _ ih => simp [ih]

theorem any_join (xss : List (List Bool)) : any (xss.map any) = any xss.join := by
  induction xss with | nil => rfl | cons _ _ ih => simp [ih]

theorem all_deMorgan : (!all xs) = any (xs.map (!·)) := by
  induction xs with | nil => rfl | cons _ _ ih => simp [ih]

theorem any_deMorgan : (!any xs) = all (xs.map (!·)) := by
  induction xs with | nil => rfl | cons _ _ ih => simp [ih]

end

end Bool
