/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.AssocList
import Std.Classes.Order
import Std.Data.Option.Lemmas
import Std.Tactic.Ext
import Std.Tactic.LeftRight
import Std.Tactic.Omega

/-!
# Ordered association lists

`OrderedAssocList` is a wrapper around `AssocList`,
with the additional invariant that the keys are in strictly increasing order.

As a consequence, an `OrderedAssocList` is determined by the `find?` function, that is
`(∀ a, l₁.find? a = l₂.find? a) → l₁ = l₂`
and this makes providing identities between operations more plausible than with `AssocList`.

We will later add another wrapper requiring that a "default" value does not appear,
so e.g. finitely supported functions can be uniquely represented.

The main operations defined are:
* `find?`, which linearly searches the list, stopping if the keys get too large.
* `insert`, which inserts a new key-value pair, maintaining the order invariant.
* `filterMapVal f`, for `f : α → β → Option γ`, which applies a function to values,
  dropping some values.
* `merge f` for `f : α → Option β → Option γ → Option δ` which merges two lists,
  dropping some values. It runs in time `O(l₁.length + l₂.length)`.
-/

namespace Std

/-!
We first define some predicates and operations in the `AssocList` namespace.

* `keysOrdered cmp l` asserts that the keys of an `l : AssocList` are strictly increasing
  with respect to a comparator `cmp`.
* `ltHeadKey? cmp a l` asserts that `a` is less than (according to `cmp`) the first key of `l`,
  or that `l` is empty.
-/

namespace AssocList

/-- The head key of an `AssocList`, or `none` if the list is empty. -/
def headKey? (l : AssocList α β) : Option α :=
  match l with
  | .nil => none
  | .cons a _ _ => some a

@[simp] theorem headKey?_nil : headKey? (.nil : AssocList α β) = none := rfl
@[simp] theorem headKey?_cons : headKey? (.cons a b t) = some a := rfl

/--
The condition that an element is less than the first key of an `AssocList`, or that list is empty.
-/
abbrev ltHeadKey? (cmp : α → α → Ordering) (a : α) (t : AssocList α β) : Prop :=
  match headKey? t with | none => True | some x => cmp a x = .lt

@[simp] theorem ltHeadKey?_nil {cmp : α → α → Ordering} :
    ltHeadKey? cmp a (.nil : AssocList α β) = True := rfl
@[simp] theorem ltHeadKey?_cons : ltHeadKey? cmp a (.cons x y t) = (cmp a x = .lt) := rfl

-- TODO redefine using ltHeadKey?

/--
The predicate that the keys of an `AssocList` are
in strictly increasing order according to the comparator `cmp`.
-/
def keysOrdered (cmp : α → α → Ordering) : AssocList α β → Prop
  | .nil => True
  | .cons _ _ .nil => True
  | .cons a _ (.cons x y t) => cmp a x = .lt ∧ keysOrdered cmp (.cons x y t)

instance instKeysOrderedDecidablePred : DecidablePred (keysOrdered cmp : AssocList α β → Prop) := by
  rintro (_|⟨a, b, _|_⟩) <;> dsimp [keysOrdered]
  · infer_instance
  · infer_instance
  · exact @instDecidableAnd _ _ _ (instKeysOrderedDecidablePred _)

@[simp] theorem keysOrdered_cons_nil : keysOrdered cmp (.cons a b nil) := trivial

-- TODO rename
theorem keysOrdered.tail (h : keysOrdered cmp (.cons a b t)) : keysOrdered cmp t :=
  match t with
  | .nil => trivial
  | .cons .. => h.2

theorem ltHeadKey?_of_keysOrdered_cons (w : keysOrdered cmp (cons a b t)) : ltHeadKey? cmp a t :=
  match t with
  | .nil => trivial
  | .cons _ _ _ => w.1

theorem ltHeadKey?_of_cons [TransCmp cmp] (w : ltHeadKey? cmp a (cons x y t))
    (h : keysOrdered cmp (cons x y t)) :
    ltHeadKey? cmp a t := by
  have h := ltHeadKey?_of_keysOrdered_cons h
  revert w h
  dsimp [ltHeadKey?]
  split
  · simp
  · exact TransCmp.lt_trans

theorem ltHeadKey?_of_le [TransCmp cmp] (h : cmp x a ≠ .gt) (w : ltHeadKey? cmp a t) :
    ltHeadKey? cmp x t := by
  revert w
  dsimp [ltHeadKey?]
  split
  · simp
  · exact TransCmp.le_lt_trans h

/--
The head key of the first list is at most the head key of the second list,
or the second list is empty.
-/
abbrev headKey?_le_headKey?
    (cmp : α → α → Ordering) (s : AssocList α β) (t : AssocList α γ) : Prop :=
  match s.headKey?, t.headKey? with
  | some a₁, some a₂ => cmp a₁ a₂ ≠ .gt
  | none, some _ => False
  | _, none => True

@[simp] theorem headKey?_le_headKey?_cons_cons :
    headKey?_le_headKey? cmp (cons a b t) (cons x y s) = (cmp a x ≠ .gt) := rfl

theorem ltHeadKey?_of_headKey?_le_headKey? [TransCmp cmp]
    (w : ltHeadKey? cmp a s) (h : headKey?_le_headKey? cmp s t) :
    ltHeadKey? cmp a t := by
  dsimp [ltHeadKey?, headKey?_le_headKey?] at *
  revert h w
  match headKey? s, headKey? t with
  | some a, some b => exact TransCmp.lt_le_trans
  | some a, none => intros; trivial
  | none, some b => simp
  | none, none => intros; trivial

theorem headKey?_le_headKey?_cons [TransCmp cmp]
    (h : keysOrdered cmp (cons x y t)) (w : headKey?_le_headKey? cmp t s) :
    headKey?_le_headKey? cmp (cons x y t) s := by
  have p := ltHeadKey?_of_keysOrdered_cons h
  dsimp [ltHeadKey?, headKey?_le_headKey?] at *
  revert p w
  match headKey? s, headKey? t with
  | some a, some b =>
    intro p w
    simp [TransCmp.lt_le_trans w p]
  | some a, none => intros; trivial
  | none, some b => simp
  | none, none => intros; trivial

theorem keysOrdered_cons {cmp : α → α → Ordering}
    (w : ltHeadKey? cmp a t) (h : keysOrdered cmp t) :
    keysOrdered cmp (.cons a b t) := by
  match t with
  | .nil => trivial
  | .cons x y s => exact ⟨w, h⟩

theorem find?_eq_none_of_ltHeadKey? {cmp : α → α → Ordering} [TransCmp cmp] [BEq α] [LawfulBEq α]
    (w : ltHeadKey? cmp a l) (h : keysOrdered cmp l) :
    l.find? a = none := by
  match l with
  | nil => rfl
  | cons x y t =>
    rw [find?]
    split
    · simp_all [OrientedCmp.cmp_refl]
    · exact find?_eq_none_of_ltHeadKey? (ltHeadKey?_of_cons w h) h.tail

/-!
# Ordered-respecting operations on `AssocList`

We now define `orderedInsert`, and `orderedMerge`,
which will later be wrapped as `OrderedAssocList.insert` and `OrderedAssocList.merge`.

We prove that with `keysOrdered` input these functions produce `keysOrdered` outputs.
We prove that same about `AssocList.filterMapVal`.
-/

/--
Insert a key-value pair into an `AssocList`,
in such a way that if the original list has keys in increasing order,
so does the result.
(Otherwise, it is inserted before the first key the new key is smaller than,
or replaces the first key the new key is equal to.)

We later wrap this as `OrderedAssocList.insert`.
-/
def orderedInsert (cmp : α → α → Ordering) (l : AssocList α β) (a : α) (b : β) : AssocList α β :=
  match l with
  | .nil => .cons a b .nil
  | .cons x y t => match w : cmp a x with
    | .lt => .cons a b l
    | .eq => .cons a b t
    | .gt => .cons x y (orderedInsert cmp t a b)

@[simp] theorem orderedInsert_nil : (nil : AssocList α β).orderedInsert cmp a b = .cons a b nil :=
  rfl

@[simp] theorem orderedInsert_cons :
    orderedInsert cmp (.cons x y t) a b = match w : cmp a x with
    | .lt => .cons a b (.cons x y t)
    | .eq => .cons a b t
    | .gt => .cons x y (orderedInsert cmp t a b) := rfl

theorem headKey?_orderedInsert {l : AssocList α β} :
    headKey? (orderedInsert cmp l a b) =
      match headKey? l with
        | none => some a
        | some x => match cmp a x with | .lt | .eq => some a | .gt => some x := by
  match l with
  | .nil => rfl
  | .cons x _ _ => dsimp [headKey?, orderedInsert]; cases cmp a x <;> rfl

theorem headKey?_orderedInsert_or (cmp) (l : AssocList α β) (a) (b) :
    headKey? (orderedInsert cmp l a b) = some a ∨
      headKey? (orderedInsert cmp l a b) = headKey? l := by
  rw [headKey?_orderedInsert]
  match l with
  | .nil => left; rfl
  | .cons x y s => dsimp; cases cmp a x <;> simp

theorem orderedInsert_keysOrdered [AntisymmCmp cmp] [OrientedCmp cmp] (h : keysOrdered cmp l) :
    keysOrdered cmp (orderedInsert cmp l a b) := by
  match l with
  | .nil => trivial
  | .cons x y t =>
    dsimp [orderedInsert]
    match w : cmp a x with
    | .lt => exact ⟨w, h⟩
    | .eq =>
      rcases AntisymmCmp.eq_of_cmp_eq w with rfl
      cases t <;> exact h
    | .gt => exact aux h w
-- I've split this step out with a name as it is useful to fill in a proof term later.
where aux [AntisymmCmp cmp] [OrientedCmp cmp] {x y t}
    (h : keysOrdered cmp (cons x y t)) (w : cmp a x = Ordering.gt) :
    keysOrdered cmp (cons x y (orderedInsert cmp t a b)) := by
        apply keysOrdered_cons
        · dsimp [ltHeadKey?]
          rcases headKey?_orderedInsert_or cmp t a b with (p|p)
          · rw [p]
            exact OrientedCmp.cmp_eq_gt.mp w
          · rw [p]
            exact ltHeadKey?_of_keysOrdered_cons h
        · apply orderedInsert_keysOrdered
          exact h.tail

theorem headKey?_le_headKey?_filterMapVal [TransCmp cmp] (h : keysOrdered cmp l) :
    headKey?_le_headKey? cmp l (l.filterMapVal f) := by
  match l with
  | .nil => simp [headKey?_le_headKey?]
  | .cons x y t =>
    simp [filterMapVal]
    match f x y with
    | none =>
      exact headKey?_le_headKey?_cons h (headKey?_le_headKey?_filterMapVal h.tail)
    | some _ => simp [OrientedCmp.cmp_refl]

theorem filterMapVal_keysOrdered [TransCmp cmp] (h : keysOrdered cmp l) :
    keysOrdered cmp (l.filterMapVal f) := by
  match l with
  | .nil => exact h
  | .cons x y t =>
    simp only [filterMapVal]
    split
    · exact filterMapVal_keysOrdered h.tail
    · apply keysOrdered_cons
      · exact ltHeadKey?_of_headKey?_le_headKey? (ltHeadKey?_of_keysOrdered_cons h)
          (headKey?_le_headKey?_filterMapVal h.tail)
      · exact filterMapVal_keysOrdered h.tail

/--
Merge two `AssocList`s,
at each stage taking the first key-value pair from whichever list has a smaller first key.
If both inputs have keys in strictly increasing order, so does the result.
(We later wrap this as `OrderedAssocList.merge`.)

We combine values using a function `f : α → Option β → Option γ → Option δ` which we call as
`f a (some b) none` when encountering a key present only in the first list (with value `b`),
`f a none (some g)` when encountering a key present only in the second list (with value `g`), and
`f a (some b) (some g)` when encountering a key present in both lists.
(Note the value of `f a none none` is never used.)
-/
def orderedMerge (cmp : α → α → Ordering) (f : α → Option β → Option γ → Option δ) :
    AssocList α β → AssocList α γ → AssocList α δ
  | .nil, .nil => nil
  | .nil, .cons a₂ g t₂ => filterMapVal (fun a g => f a none (some g)) (.cons a₂ g t₂)
  | .cons a₁ b t₁, .nil => filterMapVal (fun a b => f a (some b) none) (.cons a₁ b t₁)
  | .cons a₁ b t₁, .cons a₂ g t₂ => match cmp a₁ a₂ with
    | .lt => match (f a₁ (some b) none) with
      | some d => .cons a₁ d (orderedMerge cmp f t₁ (.cons a₂ g t₂))
      | none => orderedMerge cmp f t₁ (.cons a₂ g t₂)
    | .eq => match (f a₁ (some b) (some g)) with
      | some d => .cons a₁ d (orderedMerge cmp f t₁ t₂)
      | none => orderedMerge cmp f t₁ t₂
    | .gt => match (f a₂ none (some g)) with
      | some d => .cons a₂ d (orderedMerge cmp f (.cons a₁ b t₁) t₂)
      | none => orderedMerge cmp f (.cons a₁ b t₁) t₂
termination_by l₁ l₂ => l₁.length + l₂.length
decreasing_by all_goals simp_wf; omega

theorem ltHeadKey?_orderedMerge [TransCmp cmp]
    (h₁ : ltHeadKey? cmp a l₁) (h₂ : ltHeadKey? cmp a l₂)
    (w₁ : keysOrdered cmp l₁) (w₂ : keysOrdered cmp l₂) :
    ltHeadKey? cmp a (orderedMerge cmp f l₁ l₂) := by
  match l₁, l₂ with
  | .nil, .nil => simp [orderedMerge]
  | .nil, .cons a₂ g t₂ =>
    rw [orderedMerge]
    exact ltHeadKey?_of_headKey?_le_headKey? h₂ (headKey?_le_headKey?_filterMapVal w₂)
  | .cons a₁ b t₁, .nil =>
    rw [orderedMerge]
    exact ltHeadKey?_of_headKey?_le_headKey? h₁ (headKey?_le_headKey?_filterMapVal w₁)
  | .cons a₁ b t₁, .cons a₂ g t₂ =>
    rw [orderedMerge]
    match cmp a₁ a₂ with
    | .lt =>
      dsimp
      split
      · exact h₁
      · exact ltHeadKey?_orderedMerge (ltHeadKey?_of_cons h₁ w₁) h₂ w₁.tail w₂
    | .eq =>
      dsimp
      split
      · exact h₁
      · exact ltHeadKey?_orderedMerge (ltHeadKey?_of_cons h₁ w₁) (ltHeadKey?_of_cons h₂ w₂)
          w₁.tail w₂.tail
    | .gt =>
      dsimp
      split
      · exact h₂
      · exact ltHeadKey?_orderedMerge h₁ (ltHeadKey?_of_cons h₂ w₂) w₁ w₂.tail

theorem orderedMerge_keysOrdered [AntisymmCmp cmp] [TransCmp cmp]
    (h₁ : keysOrdered cmp l₁) (h₂ : keysOrdered cmp l₂) :
    keysOrdered cmp (orderedMerge cmp f l₁ l₂) := by
  match l₁, l₂ with
  | .nil, .nil => trivial
  | .nil, .cons a₂ g t₂ => exact filterMapVal_keysOrdered h₂
  | .cons a₁ b t₁, .nil => exact filterMapVal_keysOrdered h₁
  | .cons a₁ b t₁, .cons a₂ g t₂ =>
    rw [orderedMerge]
    match h : cmp a₁ a₂ with
    | .lt => match (f a₁ (some b) none) with
      | some d =>
        apply keysOrdered_cons
        · apply ltHeadKey?_orderedMerge (ltHeadKey?_of_keysOrdered_cons h₁) (ltHeadKey?_cons.mpr h)
            h₁.tail h₂
        · exact orderedMerge_keysOrdered h₁.tail h₂
      | none => exact orderedMerge_keysOrdered h₁.tail h₂
    | .eq => match (f a₁ (some b) (some g)) with
      | some d =>
        dsimp
        apply keysOrdered_cons
        · rcases (AntisymmCmp.eq_of_cmp_eq h) with rfl
          exact ltHeadKey?_orderedMerge (ltHeadKey?_of_keysOrdered_cons h₁)
            (ltHeadKey?_of_keysOrdered_cons h₂) h₁.tail h₂.tail
        · exact orderedMerge_keysOrdered h₁.tail h₂.tail
      | none => exact orderedMerge_keysOrdered h₁.tail h₂.tail
    | .gt => match (f a₂ none (some g)) with
      | some d =>
        apply keysOrdered_cons
        · apply ltHeadKey?_orderedMerge (ltHeadKey?_cons.mpr (OrientedCmp.cmp_eq_gt.mp h))
            (ltHeadKey?_of_keysOrdered_cons h₂) h₁ h₂.tail
        · exact orderedMerge_keysOrdered h₁ h₂.tail
      | none => exact orderedMerge_keysOrdered h₁ h₂.tail

/--
Find the value associated to a key by traversing left to right,
short-circuiting once we are considering larger keys.
-/
def orderedFind? (cmp : α → α → Ordering) (l : AssocList α β) (x : α) : Option β :=
  match l with
  | .nil => none
  | .cons a b t => match cmp x a with
    | .lt => none
    | .eq => some b
    | .gt => orderedFind? cmp t x

@[simp] theorem orderedFind?_nil {cmp : α → α → Ordering} :
    orderedFind? cmp (nil : AssocList α β) x = none := rfl

theorem orderedFind?_eq_find?
    {cmp : α → α → Ordering} [AntisymmCmp cmp] [TransCmp cmp] [BEq α] [LawfulBEq α]
    (l : AssocList α β) (h : l.keysOrdered cmp) (x : α) : l.orderedFind? cmp x = l.find? x := by
  match l with
  | .nil => rfl
  | .cons a b t =>
    rw [find?, AssocList.orderedFind?]
    split
    · split
      · simp_all [OrientedCmp.cmp_refl]
      · rw [AssocList.find?_eq_none_of_ltHeadKey? (cmp := cmp)]
        · exact AssocList.ltHeadKey?_of_le (by simp_all)
            (AssocList.ltHeadKey?_of_keysOrdered_cons h)
        · exact h.tail
    · simp_all [AntisymmCmp.eq_of_cmp_eq ‹_›]
    · split
      · simp_all [OrientedCmp.cmp_refl]
      · apply orderedFind?_eq_find? _ h.tail

theorem orderedFind?_eq_none_of_ltHeadKey? (l : AssocList α β) (w : ltHeadKey? cmp x l) :
    orderedFind? cmp l x = none := by
  match l with
  | .nil => rfl
  | .cons a b t =>
    match p : cmp x a with
    | .lt => simp [orderedFind?, p]
    | .eq => simp_all [ltHeadKey?]
    | .gt => simp_all [ltHeadKey?]

theorem orderedFind?_cons [TransCmp cmp]
    (h : (AssocList.cons a b t).keysOrdered cmp) :
    orderedFind? cmp (.cons a b t) x = if cmp x a = .eq then some b else orderedFind? cmp t x := by
  simp only [find?, AssocList.orderedFind?]
  split <;> rename_i w <;> simp only [w, ite_true, ite_false]
  rw [AssocList.orderedFind?_eq_none_of_ltHeadKey?]
  simp only [ltHeadKey?, headKey?]
  split <;> rename_i h'
  · trivial
  · apply TransCmp.lt_trans w
    revert h'
    split
    · simp
    · simp only [Option.some.injEq]
      rintro rfl
      exact h.1

@[simp] theorem orderedFind?_cons_self [OrientedCmp cmp] :
    orderedFind? cmp (.cons a b t) a = some b := by
  simp [find?, AssocList.orderedFind?, OrientedCmp.cmp_refl]

theorem orderedFind?_orderedInsert {cmp : α → α → Ordering} [AntisymmCmp cmp] [TransCmp cmp]
    (l : AssocList α β) (h : keysOrdered cmp l) (a : α) (b : β) :
    (orderedInsert cmp l a b).orderedFind? cmp x =
      if cmp x a = .eq then some b else l.orderedFind? cmp x := by
  match l with
  | .nil =>
    simp only [orderedInsert, orderedFind?_cons, keysOrdered_cons_nil]
  | .cons a' b' t =>
    simp only [orderedInsert_cons]
    split <;> rename_i h₁
    · apply orderedFind?_cons
      exact ⟨h₁, h⟩
    · rcases AntisymmCmp.eq_of_cmp_eq h₁
      rw [orderedFind?_cons h, orderedFind?_cons]
      · split <;> rfl
      · cases t <;> exact h
    · rw [orderedFind?_cons, orderedFind?_orderedInsert t h.tail, orderedFind?_cons h]
      · split <;> rename_i h₂
        · rcases (AntisymmCmp.eq_of_cmp_eq h₂).symm
          simp_all [OrientedCmp.cmp_eq_gt]
        · rfl
      · exact orderedInsert_keysOrdered.aux h h₁
termination_by l.length

theorem orderedFind?_orderedInsert_self {cmp : α → α → Ordering} [AntisymmCmp cmp] [TransCmp cmp]
    (l : AssocList α β) (h : keysOrdered cmp l)  (a : α) (b : β) :
    (orderedInsert cmp l a b).orderedFind? cmp a = some b := by
  simp [h, orderedFind?_orderedInsert, OrientedCmp.cmp_refl]

-- theorem orderedInsert_contains {cmp : α → α → Ordering} [BEq α] (l : AssocList α β) (a : α) (b : β) :
--     (l.orderedInsert cmp a b).contains x = ((cmp x a = .eq) || l.contains x) := by
--   sorry

-- theorem orderedInsert_contains_self {cmp : α → α → Ordering} [BEq α] (l : AssocList α β) (a : α) (b : β) :
--     (l.orderedInsert cmp a b).contains a = true := by
--   sorry

/--
If two `AssocList`s have ordered keys
we can check whether they are equal by checking if their `find?` functions are equal.
-/
theorem ext_orderedKeys
    (cmp : α → α → Ordering) [AntisymmCmp cmp] [TransCmp cmp]
    {l₁ l₂ : AssocList α β} (h₁ : l₁.keysOrdered cmp) (h₂ : l₂.keysOrdered cmp)
    (w : ∀ a, l₁.orderedFind? cmp a = l₂.orderedFind? cmp a) : l₁ = l₂ := by
  match w₁ : l₁, w₂ : l₂ with
  | .nil, .nil => rfl
  | .cons a b t, .nil =>
    exfalso
    specialize w a
    simp_all
  | .nil, .cons a b t =>
    exfalso
    specialize w a
    simp_all
  | .cons a₁ b₁ t₁, .cons a₂ b₂ t₂ =>
    match h : cmp a₁ a₂ with
    | .lt =>
      exfalso
      have w₂ : l₂.orderedFind? cmp a₁ = none := by
        rw [w₂, orderedFind?_eq_none_of_ltHeadKey? _ h]
      specialize w a₁
      simp [orderedFind?_cons_self] at w
      simp_all [orderedFind?_eq_find?]
    | .eq =>
      rcases AntisymmCmp.eq_of_cmp_eq h
      have w' := w a₁
      simp only [orderedFind?_cons_self, Option.some.injEq] at w'
      congr
      apply ext_orderedKeys cmp h₁.tail h₂.tail
      intro a
      specialize w a
      rw [orderedFind?_cons h₁, orderedFind?_cons h₂] at w
      split at w <;> rename_i h
      · rcases AntisymmCmp.eq_of_cmp_eq h
        rw [orderedFind?_eq_none_of_ltHeadKey?, orderedFind?_eq_none_of_ltHeadKey?]
        apply ltHeadKey?_of_keysOrdered_cons h₂
        apply ltHeadKey?_of_keysOrdered_cons h₁
      · exact w
    | .gt =>
      exfalso
      have w₁ : l₁.orderedFind? cmp a₂ = none := by
        rw [w₁, orderedFind?_eq_none_of_ltHeadKey? _ (OrientedCmp.cmp_eq_gt.mp h)]
      specialize w a₂
      simp [orderedFind?_cons_self] at w
      simp_all [orderedFind?_eq_find?]

@[simp]
theorem orderedFind?_filterMapVal {cmp : α → α → Ordering} [AntisymmCmp cmp] [TransCmp cmp]
    {l : AssocList α β} (h : keysOrdered cmp l) :
    (filterMapVal f l).orderedFind? cmp a = (l.orderedFind? cmp a).bind (fun b => f a b) := by
  -- This isn't true at the level of `AssocList`; we need uniqueness of keys.
  match l with
  | .nil => rfl
  | .cons x y t =>
    simp only [filterMapVal_cons, orderedFind?_cons, h]
    split
    · rw [orderedFind?_filterMapVal h.tail]
      split <;> rename_i h'
      · have h' := AntisymmCmp.eq_of_cmp_eq h'
        rw [orderedFind?_eq_none_of_ltHeadKey?]
        · simp_all
        · rcases h' with rfl
          exact ltHeadKey?_of_keysOrdered_cons h
      · rfl
    · rw [orderedFind?_cons]
      · split <;> rename_i h'
        · simp_all [AntisymmCmp.eq_of_cmp_eq h']
        · rw [orderedFind?_filterMapVal h.tail]
      · exact keysOrdered_cons
          (ltHeadKey?_of_headKey?_le_headKey? (ltHeadKey?_of_keysOrdered_cons h)
            (headKey?_le_headKey?_filterMapVal h.tail))
          (filterMapVal_keysOrdered h.tail)
termination_by l.length

theorem filterMapVal_filterMapVal {cmp : α → α → Ordering} [AntisymmCmp cmp] [TransCmp cmp]
    {f : α → γ → Option δ} {g : α → β → Option γ}
    {l : AssocList α β} (h : keysOrdered cmp l) :
    filterMapVal f (filterMapVal g l) =
      filterMapVal (fun a b => (g a b).bind (fun c => f a c)) l := by
  apply ext_orderedKeys (cmp := cmp)
  · exact filterMapVal_keysOrdered (filterMapVal_keysOrdered h)
  · exact filterMapVal_keysOrdered h
  · intro a
    rw [orderedFind?_filterMapVal, orderedFind?_filterMapVal h, orderedFind?_filterMapVal h]
    · ext d
      simp only [orderedFind?_filterMapVal, h, Option.mem_def, Option.bind_eq_some]
      constructor
      · rintro ⟨c, ⟨⟨b, hb, hc⟩, hd⟩⟩
        refine ⟨b, hb, c, hc, hd⟩
      · rintro ⟨b, hb, c, hc, hd⟩
        refine ⟨c, ⟨⟨b, hb, hc⟩, hd⟩⟩
    · exact filterMapVal_keysOrdered h

end AssocList

/--
An `OrderedAssocList` is an `AssocList` with the additional invariant that
the keys are in strictly increasing order according to some specified comparator function.
-/
structure OrderedAssocList {α : Type u} (cmp : α → α → Ordering) (β : Type v) where
  /-- The underlying `AssocList` of an `OrderedAssocList`. -/
  list : AssocList α β
  /-- The invariant that the keys are in strictly increasing order according to `cmp`. -/
  keysOrdered : list.keysOrdered cmp

namespace OrderedAssocList

variable {α : Type u} {cmp : α → α → Ordering}

/-- The empty `OrderedAssocList`. -/
def nil : OrderedAssocList cmp β := ⟨.nil, trivial⟩

/-- The length of an `OrderedAssocList`. -/
def length (l : OrderedAssocList cmp β) : Nat := l.list.length

@[simp] theorem length_nil : length (nil : OrderedAssocList cmp β) = 0 := rfl
@[simp] theorem length_mk_cons : length ⟨.cons a b t, h⟩ = length ⟨t, h.tail⟩ + 1 :=
  rfl

/-- The first key-value pair in an `OrderedAssocList`. -/
def head? (l : OrderedAssocList cmp β) : Option (α × β) :=
  match l with
  | ⟨.nil, _⟩ => none
  | ⟨.cons a b _, _⟩ => some (a, b)

/-- The tail of an `OrderedAssocList`. -/
def tail (l : OrderedAssocList cmp β) : OrderedAssocList cmp β :=
  match l with
  | ⟨.nil, _⟩ => l
  | ⟨.cons _ _ t, h⟩ => ⟨t, h.tail⟩

@[simp] theorem length_tail : length (tail l) = length l - 1 := by
  match l with
  | ⟨.nil, _⟩ => rfl
  | ⟨.cons _ _ _, _⟩ => rfl

/--
Find the value associated to a key by traversing left to right,
short-circuiting once we are considering larger keys.
-/
def find? (l : OrderedAssocList cmp β) (x : α) : Option β :=
  l.list.orderedFind? cmp x

@[simp] theorem find?_nil : find? (nil : OrderedAssocList cmp β) x = none := rfl
@[simp] theorem find?_mk_nil : find? ⟨.nil, h⟩ x = none := rfl

/-- The first key in an `OrderedAssocList`, or `none` if the list is empty. -/
def headKey? (l : OrderedAssocList cmp β) : Option α := l.list.headKey?

@[simp] theorem headKey?_nil : headKey? (nil : OrderedAssocList cmp β) = none := rfl
@[simp] theorem headKey?_mk_cons : headKey? ⟨.cons a b t, h⟩ = some a := rfl

/-- Either `a` is less than the first key of `l`, or `l` is empty. -/
def ltHeadKey? (a : α) (l : OrderedAssocList cmp β) : Prop := AssocList.ltHeadKey? cmp a l.list

/-- The head key of a tail is either `none`, or greater than the original head key. -/
theorem headKey?_tail (h : AssocList.keysOrdered cmp (.cons a b t)) :
    ltHeadKey? a ⟨t, h.tail⟩ := by
  dsimp [ltHeadKey?]
  match t with
  | .nil => trivial
  | .cons _ _ _ => exact h.1

theorem find?_eq_none_of_ltHeadKey? (l : OrderedAssocList cmp β) (w : ltHeadKey? x l) :
    find? l x = none :=
  AssocList.orderedFind?_eq_none_of_ltHeadKey? _ w

theorem find?_mk_cons [TransCmp cmp]
    {h : (AssocList.cons a b t).keysOrdered cmp} :
    find? ⟨.cons a b t, h⟩ x = if cmp x a = .eq then some b else find? ⟨t, h.tail⟩ x := by
  simp only [find?, AssocList.orderedFind?]
  split <;> rename_i w <;> simp only [w, ite_true, ite_false]
  rw [AssocList.orderedFind?_eq_none_of_ltHeadKey?]
  have p := headKey?_tail h
  revert p
  simp only [ltHeadKey?, AssocList.ltHeadKey?]
  split
  · trivial
  · exact TransCmp.lt_trans w

@[simp] theorem find?_mk_cons_self [OrientedCmp cmp] {h : (AssocList.cons a b t).keysOrdered cmp} :
    find? ⟨.cons a b t, h⟩ a = some b := by
  simp [find?, AssocList.orderedFind?, OrientedCmp.cmp_refl]

theorem ext_list {l₁ l₂ : OrderedAssocList cmp β} (w : l₁.list = l₂.list) : l₁ = l₂ := by
  cases l₁; cases l₂; congr

@[ext] theorem ext [AntisymmCmp cmp] [TransCmp cmp] {l₁ l₂ : OrderedAssocList cmp β}
    (w : ∀ a, l₁.find? a = l₂.find? a) : l₁ = l₂ := by
  apply ext_list
  apply AssocList.ext_orderedKeys _ l₁.keysOrdered l₂.keysOrdered
  simpa [find?, AssocList.orderedFind?_eq_find?, l₁.keysOrdered, l₂.keysOrdered] using w

/-- Check if an `OrderedAssocList` contains a specific key. -/
def contains (l : OrderedAssocList cmp β) (x : α) : Bool := (l.find? x).isSome

@[simp] theorem contains_nil : contains (nil : OrderedAssocList cmp β) x = false := rfl
@[simp] theorem contains_mk_cons_self [OrientedCmp cmp]
    {h : (AssocList.cons a b t).keysOrdered cmp} :
    contains ⟨.cons a b t, h⟩ a = true := by
  simp [contains]

/--
Prepend a key-value pair,
requiring a proof that the key is smaller than the existing smallest key.
-/
def cons (a : α) (b : β) (l : OrderedAssocList cmp β) (w : ltHeadKey? a l) :
    OrderedAssocList cmp β :=
  match l with
  | ⟨.nil, _⟩ => ⟨.cons a b .nil, trivial⟩
  | ⟨.cons x y t, h⟩ => ⟨.cons a b (.cons x y t), ⟨w, h⟩⟩

@[simp] theorem list_cons : (cons a b l w).list = .cons a b l.list := by
  dsimp [cons]
  match l with
  | ⟨.nil, _⟩ => rfl
  | ⟨.cons x y t, h⟩ => rfl

@[simp] theorem find?_cons [TransCmp cmp] {l : OrderedAssocList cmp β} {w} :
    (cons a b l w).find? x = if cmp x a = .eq then some b else l.find? x := by
  simp only [cons]
  split <;> simp [find?_mk_cons]

@[simp] theorem headKey?_cons : headKey? (cons a b l w) = some a := by
  match l with
  | ⟨.nil, _⟩
  | ⟨.cons _ _ _, _⟩ => rfl

section insert
variable [AntisymmCmp cmp]

section
variable [OrientedCmp cmp]

/--
Insert a key-value pair into an `OrderedAssocList`.
This replaces the current value if the key is already present,
and otherwise inserts it before the first key which is greater than the inserted key.
-/
def insert (l : OrderedAssocList cmp β) (a : α) (b : β) : OrderedAssocList cmp β :=
  ⟨l.list.orderedInsert cmp a b, AssocList.orderedInsert_keysOrdered l.keysOrdered⟩

@[simp] theorem insert_mk_nil :
    insert (⟨.nil, h⟩ : OrderedAssocList cmp β) a b = ⟨.cons a b .nil, trivial⟩ := rfl

@[simp] theorem insert_mk_cons :
    insert (⟨.cons x y t, h⟩ : OrderedAssocList cmp β) a b = match w : cmp a x with
    | .lt => ⟨.cons a b (.cons x y t), ⟨w, h⟩⟩
    | .eq => ⟨.cons a b t, by
        cases (AntisymmCmp.eq_of_cmp_eq w); cases t <;> exact h⟩
    | .gt => .cons x y (insert ⟨t, h.tail⟩ a b) (AssocList.ltHeadKey?_of_keysOrdered_cons
        (AssocList.orderedInsert_keysOrdered.aux h w)) := by
  dsimp [insert, AssocList.orderedInsert]
  congr
  split <;> simp

theorem length_insert_ne_zero {l : OrderedAssocList cmp β} : (insert l a b).length ≠ 0 := by
  match l with
  | ⟨.nil, _⟩ => simp
  | ⟨.cons x y t, _⟩ =>
    dsimp [insert, AssocList.orderedInsert, length]
    split <;> simp

end

variable [TransCmp cmp]

theorem find?_insert (l : OrderedAssocList cmp β) (a : α) (b : β) :
    (insert l a b).find? x = if cmp x a = .eq then some b else l.find? x :=
  AssocList.orderedFind?_orderedInsert l.list l.keysOrdered a b

theorem find?_insert_self (l : OrderedAssocList cmp β) (a : α) (b : β) :
    (insert l a b).find? a = some b := by
  simp [find?_insert, OrientedCmp.cmp_refl]

-- theorem insert_contains (l : OrderedAssocList cmp β) (a : α) (b : β) :
--     (l.insert a b).contains x = ((cmp x a = .eq) || l.contains x) := by
--   simp only [contains, find?_insert]
--   split <;> rename_i h
--   · simp [h]
--   · cases find? l x <;> simp [h]

-- theorem insert_contains_self (l : OrderedAssocList cmp β) (a : α) (b : β) :
--     (l.insert a b).contains a = true := by
--   simp [insert_contains, OrientedCmp.cmp_refl]

end insert

section filterMapVal

variable [TransCmp cmp]

/--
Apply a function to each key-value pair,
either replacing the value or dropping it if the function returns `none`.
-/
def filterMapVal (f : α → β → Option δ) (l : OrderedAssocList cmp β) :
    OrderedAssocList cmp δ :=
  ⟨l.list.filterMapVal f, AssocList.filterMapVal_keysOrdered l.keysOrdered⟩

@[simp]
theorem find?_filterMapVal [AntisymmCmp cmp] (l : OrderedAssocList cmp β) :
    (filterMapVal f l).find? a = (l.find? a).bind (fun b => f a b) :=
  AssocList.orderedFind?_filterMapVal l.keysOrdered

theorem filterMapVal_filterMapVal [AntisymmCmp cmp] [TransCmp cmp]
    {f : α → γ → Option δ} {g : α → β → Option γ}
    {l : OrderedAssocList cmp β} :
    filterMapVal f (filterMapVal g l) =
      filterMapVal (fun a b => (g a b).bind (fun c => f a c)) l := by
  apply ext_list
  exact AssocList.filterMapVal_filterMapVal l.keysOrdered

end filterMapVal

section merge

variable [AntisymmCmp cmp] [TransCmp cmp]

/--
Merge two `OrderedAssocList`s using a function `α → Option β → Option γ → Option δ`,
dropping values where the function returns `none`.
-/
def merge (f : α → Option β → Option γ → Option δ)
    (l₁ : OrderedAssocList cmp β) (l₂ : OrderedAssocList cmp γ) : OrderedAssocList cmp δ :=
  ⟨AssocList.orderedMerge cmp f l₁.list l₂.list,
    AssocList.orderedMerge_keysOrdered l₁.keysOrdered l₂.keysOrdered⟩

@[simp] theorem list_merge {l₁ : OrderedAssocList cmp β} :
    (merge f l₁ l₂).list = AssocList.orderedMerge cmp f l₁.list l₂.list :=
  rfl

@[simp] theorem merge_nil_nil {f : α → Option β → Option γ → Option δ} :
    merge f (nil : OrderedAssocList cmp β) nil = nil := rfl

@[simp] theorem merge_mk_nil_mk_cons {f : α → Option β → Option γ → Option δ} :
    merge f (⟨.nil, h⟩ : OrderedAssocList cmp β) ⟨.cons x' y' t', h'⟩ =
      filterMapVal (fun a g => f a none (some g)) ⟨.cons x' y' t', h'⟩ := rfl

@[simp] theorem merge_mk_cons_mk_nil {f : α → Option β → Option γ → Option δ} :
    merge f ⟨.cons x y t, h⟩ (⟨.nil, h'⟩ : OrderedAssocList cmp γ) =
      filterMapVal (fun a b => f a (some b) none) ⟨.cons x y t, h⟩ := rfl

private theorem merge_mk_cons_mk_cons_list
    (f : α → Option β → Option γ → Option δ) (x y t h x' y' t' h') :
    (merge f (⟨.cons x y t, h⟩ : OrderedAssocList cmp β) ⟨.cons x' y' t', h'⟩).list =
      match cmp x x' with
      | .lt => match f x (some y) none with
        | none => AssocList.orderedMerge cmp f t (.cons x' y' t')
        | some d => .cons x d (AssocList.orderedMerge cmp f t (.cons x' y' t'))
      | .eq => match f x (some y) (some y') with
        | none => AssocList.orderedMerge cmp f t t'
        | some d => .cons x d (AssocList.orderedMerge cmp f t t')
      | .gt => match f x' none (some y') with
        | none => AssocList.orderedMerge cmp f (.cons x y t) t'
        | some d => .cons x' d (AssocList.orderedMerge cmp f (.cons x y t) t') := by
  dsimp [merge]
  rw [AssocList.orderedMerge]
  split <;> split <;> simp_all

private theorem merge_mk_cons_mk_cons {f : α → Option β → Option γ → Option δ} :
    merge f (⟨.cons x y t, h⟩ : OrderedAssocList cmp β) ⟨.cons x' y' t', h'⟩ =
      match i: cmp x x' with
      | .lt => match w : f x (some y) none with
        | none => merge f ⟨t, h.tail⟩ ⟨.cons x' y' t', h'⟩
        | some d => ⟨.cons x d (merge f ⟨t, h.tail⟩ ⟨.cons x' y' t', h'⟩).list, by
            have p := merge_mk_cons_mk_cons_list f x y t h x' y' t' h'
            simp only [w, i] at p
            simp only [list_merge]
            simp only [← p]
            exact (merge f _ _).keysOrdered⟩
      | .eq => match w : f x (some y) (some y') with
        | none => merge f ⟨t, h.tail⟩ ⟨t', h'.tail⟩
        | some d => ⟨.cons x d (merge f ⟨t, h.tail⟩ ⟨t', h'.tail⟩).list, by
            have p := merge_mk_cons_mk_cons_list f x y t h x' y' t' h'
            simp only [w, i] at p
            simp only [list_merge]
            simp only [← p]
            exact (merge f _ _).keysOrdered⟩
      | .gt => match w : f x' none (some y') with
        | none => merge f ⟨.cons x y t, h⟩ ⟨t', h'.tail⟩
        | some d => ⟨.cons x' d (merge f ⟨.cons x y t, h⟩ ⟨t', h'.tail⟩).list, by
            have p := merge_mk_cons_mk_cons_list f x y t h x' y' t' h'
            simp only [w, i] at p
            simp only [list_merge]
            simp only [← p]
            exact (merge f _ _).keysOrdered⟩ := by
  apply ext_list
  simp only [merge_mk_cons_mk_cons_list]
  split <;> split <;> simp_all [merge]

@[simp] theorem find?_merge {f : α → Option β → Option γ → Option δ}
    (hf : f a none none = none) {l₁ : OrderedAssocList cmp β} {l₂} :
    (merge f l₁ l₂).find? a = f a (l₁.find? a) (l₂.find? a) := by
  match l₁, l₂ with
  | ⟨.nil, _⟩, ⟨.nil, _⟩ => exact hf.symm
  | ⟨.nil, _⟩, ⟨.cons x' y' t', h'⟩ =>
    rw [merge_mk_nil_mk_cons, find?_filterMapVal, find?_mk_nil, Option.bind]
    split <;> (rename_i w; rw [w])
    rw [hf]
  | ⟨.cons x y t, h⟩, ⟨.nil, _⟩ =>
    rw [merge_mk_cons_mk_nil, find?_filterMapVal, find?_mk_nil, Option.bind]
    split <;> (rename_i w; rw [w])
    rw [hf]
  | ⟨.cons x y t, h⟩, ⟨.cons x' y' t', h'⟩ =>
    rw [merge_mk_cons_mk_cons]
    split <;> rename_i h₁
    · split <;> rename_i h₂
      · rw [find?_merge hf]
        rw [find?_mk_cons (a := x)]
        split <;> rename_i h₃
        · rcases AntisymmCmp.eq_of_cmp_eq h₃ with rfl
          rw [find?_eq_none_of_ltHeadKey?, find?_eq_none_of_ltHeadKey?, hf]
          · simp_all
          · exact h₁
          · exact AssocList.ltHeadKey?_of_keysOrdered_cons h
        · rfl
      · rw [find?_mk_cons]
        split <;> rename_i h₃
        · rcases AntisymmCmp.eq_of_cmp_eq h₃ with rfl
          simp only [← h₂, find?_mk_cons_self]
          rw [find?_eq_none_of_ltHeadKey?]
          exact h₁
        · rw [find?_merge hf, find?_mk_cons (a := x), if_neg h₃]
    · rcases (AntisymmCmp.eq_of_cmp_eq h₁)
      split <;> rename_i h₂
      · rw [find?_merge hf]
        rw [find?_mk_cons, find?_mk_cons]
        split <;> rename_i h₃
        · rcases (AntisymmCmp.eq_of_cmp_eq h₃)
          rw [find?_eq_none_of_ltHeadKey?, find?_eq_none_of_ltHeadKey?, hf, h₂]
          · exact AssocList.ltHeadKey?_of_keysOrdered_cons h'
          · exact AssocList.ltHeadKey?_of_keysOrdered_cons h
        · rfl
      · rw [find?_mk_cons]
        split <;> rename_i h₃
        · rcases (AntisymmCmp.eq_of_cmp_eq h₃)
          rw [find?_mk_cons_self, find?_mk_cons_self, h₂]
        · rw [find?_merge hf, find?_mk_cons (a := x), if_neg h₃, find?_mk_cons (a := x), if_neg h₃]
    · split <;> rename_i h₂
      · rw [find?_merge hf]
        rw [find?_mk_cons (a := x')]
        split <;> rename_i h₃
        · rcases (AntisymmCmp.eq_of_cmp_eq h₃)
          rw [find?_eq_none_of_ltHeadKey?, find?_eq_none_of_ltHeadKey?, hf]
          · exact h₂.symm
          · exact AssocList.ltHeadKey?_of_keysOrdered_cons h'
          · exact OrientedCmp.cmp_eq_gt.mp h₁
        · rfl
      · rw [find?_mk_cons]
        split <;> rename_i h₃
        · rcases (AntisymmCmp.eq_of_cmp_eq h₃)
          simp only [find?_mk_cons_self]
          rw [find?_eq_none_of_ltHeadKey?, h₂]
          exact OrientedCmp.cmp_eq_gt.mp h₁
        · rw [find?_merge hf, find?_mk_cons (a := x'), if_neg h₃]

@[nolint unusedArguments] -- falsely reports that `hf` is not used.
theorem merge_comm
    (f : α → Option β → Option γ → Option δ) (g : α → Option γ → Option β → Option δ)
    (hf : ∀ a, f a none none = none) (hg : ∀ a, g a none none = none)
    (w : ∀ a x y, f a x y = g a y x)
    (l₁ : OrderedAssocList cmp β) (l₂) : merge f l₁ l₂ = merge g l₂ l₁ := by
  ext
  simp [w, hf, hg]

theorem merge_assoc
    (f₁ : α → Option β₁ → Option β₂ → Option γ₁) (f₂ : α → Option γ₁ → Option β₃ → Option ε)
    (g₁ : α → Option β₂ → Option β₃ → Option γ₂) (g₂ : α → Option β₁ → Option γ₂ → Option ε)
    (hf₁ : ∀ a, f₁ a none none = none) (hf₂ : ∀ a, f₂ a none none = none)
    (hg₁ : ∀ a, g₁ a none none = none) (hg₂ : ∀ a, g₂ a none none = none)
    (w : ∀ a x y z, f₂ a (f₁ a x y) z = g₂ a x (g₁ a y z))
    (l₁ : OrderedAssocList cmp β₁) (l₂) (l₃) :
    merge f₂ (merge f₁ l₁ l₂) l₃ = merge g₂ l₁ (merge g₁ l₂ l₃) := by
  ext
  simp [w, hf₁, hf₂, hg₁, hg₂]

/--
Add two `OrderedAssocList`s, taking the value from one list if the other value is missing.
(That is, treating missing values as `0`.)
-/
def add [Add β] (l₁ : OrderedAssocList cmp β) (l₂ : OrderedAssocList cmp β) :
    OrderedAssocList cmp β :=
  merge (fun _ => addOption) l₁ l₂
where
  /-- Add two values, treating missing values as `0`. -/
  addOption : Option β → Option β → Option β
    | some x, some y => some (x + y)
    | some x, none => some x
    | none, some y => some y
    | none, none => none

-- This statement will look better on the version of `OrderedAssocList` with default values,
-- where we can just write `(add l₁ l₂).find a = l₁.find a + l₂.find a`.

@[simp] theorem find?_add [Add β] {l₁ : OrderedAssocList cmp β} :
    (add l₁ l₂).find? a =
      match l₁.find? a, l₂.find? a with
      | some x, some y => some (x + y)
      | some x, none => some x
      | none, some y => some y
      | none, none => none := by
  rw [add, find?_merge rfl]
  rfl

/--
Multiply two `OrderedAssocList`s,
dropping any values where the corresponding value in the other list is missing.
(That is, treating missing values as `0`.)
-/
def mul [Mul β] (l₁ : OrderedAssocList cmp β) (l₂ : OrderedAssocList cmp β) :
    OrderedAssocList cmp β :=
  merge (fun _ => mulOption) l₁ l₂
where
  /-- Multiply two values, treating missing values as `0`. -/
  mulOption : Option β → Option β → Option β
    | some x, some y => some (x * y)
    | some _, none => none
    | none, some _ => none
    | none, none => none

@[simp] theorem find?_mul [Mul β] {l₁ : OrderedAssocList cmp β} :
    (mul l₁ l₂).find? a =
      match l₁.find? a, l₂.find? a with
      | some x, some y => some (x * y)
      | some _, none => none
      | none, some _ => none
      | none, none => none := by
  rw [mul, find?_merge rfl]
  rfl

end merge

end OrderedAssocList
