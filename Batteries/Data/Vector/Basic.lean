/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Francois Dorais
-/

import Batteries.Data.Array
import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas
import Batteries.Tactic.Lint.Misc

/-!
## Vectors
`Vector α n` is an array with a statically fixed size `n`.
It combines the benefits of Lean's special support for `Arrays`
that offer `O(1)` accesses and in-place mutations for arrays with no more than one reference,
with static guarantees about the size of the underlying array.
-/

/-- `Vector α n` is an `Array α` whose size is statically fixed to `n` -/
structure Vector (α : Type u) (n : Nat) where
  /--Internally, a vector is stored as an array for fast access-/
  toArray : Array α
  /--`size_eq` fixes the size of `toArray` statically-/
  size_eq : toArray.size = n
deriving Repr, BEq, DecidableEq

namespace Vector

open Array

/-- Syntax for `Vector α n` -/
syntax "#v[" withoutPosition(sepBy(term, ", ")) "]" : term

open Lean in
macro_rules
  | `(#v[ $elems,* ]) => `(Vector.mk (n := $(quote elems.getElems.size)) #[$elems,*] rfl)

/-- `Vector.size` gives the size of a vector. -/
@[nolint unusedArguments]
def size (_ : Vector α n) : Nat := n

/-- `Vector.empty` produces an empty vector -/
def empty : Vector α 0 := ⟨Array.empty, rfl⟩

/-- Make an empty vector with pre-allocated capacity-/
def mkEmpty (capacity : Nat) : Vector α 0 := ⟨Array.mkEmpty capacity, rfl⟩

/-- Makes a vector of size `n` with all cells containing `v` -/
def mkVector (n : Nat) (v : α) : Vector α n :=
  ⟨mkArray n v, proof⟩
  where
    proof := by
      rw [size_mkArray]

/--
The Inhabited instance for `Vector α n` with `[Inhabited α]` produces a vector of size `n`
with all its elements equal to the `default` element of type `α`
-/
instance [Inhabited α] : Inhabited (Vector α n) where
  default := mkVector n default

/-- The list obtained from a vector. -/
def toList (v : Vector α n) : List α := v.1.1

/-- nth element of a vector, indexed by a `Fin` type. -/
abbrev get (v : Vector α n) (i : Fin n) : α :=
  v.1.get <| i.cast v.2.symm

/-- `Vector α n` nstance for the `GetElem` typeclass. -/
instance : GetElem (Vector α n) Nat α fun _ i => i < n where
  getElem := fun x i h => get x ⟨i, h⟩

/--
`getD v i v₀` gets the `iᵗʰ` element of v if valid.
Otherwise it returns `v₀` by default
-/
abbrev getD (v : Vector α n) (i : Nat) (v₀ : α) : α := Array.getD v.toArray i v₀

/--`get! v i` gets the `iᵗʰ` element of v if valid, else panics -/
def get! [Inhabited α] (v : Vector α n) (i : Nat) : α := v.toArray.get! i

/-- `get? v i` gets `some v[i]` if `i` is a valid index, otherwise `none` -/
def get? (v : Vector α n) (i : Nat) : Option α := Array.get? v.toArray i

/--
`v.back! v` gets the last element of the vector.
panics if `v` is empty.
-/
abbrev back! [Inhabited α] (v : Vector α n) : α := Vector.get! v (n - 1)

/--
`v.back?` gets the last element `x` of the array as `some x`
if it exists. Else the vector is empty and it returns `none`
-/
def back? (v : Vector α n) : Option α :=
  v.get? (n - 1)

/-- `Vector.head` produces the head of a vector -/
abbrev head (v : Vector α (n+1)) := v.get 0

/-- `push v x` pushes `x` to the end of vector `v` in O(1) time -/
def push (x : α) (v : Vector α n)  : Vector α (n + 1) :=
  ⟨v.toArray.push x, proof⟩
  where
    proof := by
      simp only [size_push, Nat.reduceEqDiff]
      exact v.size_eq

/--
Sets an element in a vector using a Fin index.

This will perform the update destructively provided that a has a reference count of 1 when called.
-/
def set (v : Vector α n) (i : Fin n) (x : α) : Vector α n :=
  ⟨v.toArray.set (Fin.cast v.size_eq.symm i) x, proof⟩
  where
    proof := by {rw [size_set]; exact v.size_eq}

/--
`setN v i h x` sets an element in a vector using a Nat index which is provably valid.
By default a proof by `get_elem_tactic` is provided.

This will perform the update destructively provided that a has a reference count of 1 when called.
-/
def setN (v : Vector α n) (i : Nat) (h : i < n := by get_elem_tactic) (x : α) : Vector α n :=
  ⟨v.toArray.set (Fin.cast v.size_eq.symm ⟨i, h⟩) x, proof⟩
  where
    proof := by {rw [size_set]; exact v.size_eq}
/--
Sets an element in a vector, or do nothing if the index is out of bounds.

This will perform the update destructively provided that a has a reference count of 1 when called.
-/
def setD (v : Vector α n) (i : Nat) (x : α) : Vector α n :=
  ⟨v.toArray.setD i x, proof⟩
  where
    proof := by
      rw [size_setD]
      exact v.size_eq

/--
Sets an element in an array, or panic if the index is out of bounds.

This will perform the update destructively provided that a has a reference count of 1 when called.
-/
def set! (v : Vector α n) (i : Nat) (x : α) : Vector α n :=
  ⟨v.toArray.set! i x, proof⟩
  where
    proof := by
      rw [set!_is_setD, size_setD]
      exact v.size_eq

/-- Appends a vector to another. -/
def append : Vector α n → Vector α m → Vector α (n + m)
  | ⟨a₁, h₁⟩, ⟨a₂, h₂⟩ => ⟨a₁ ++ a₂, by rw[Array.size_append, ←h₁,←h₂]⟩

instance : HAppend (Vector α n) (Vector α m) (Vector α (n + m)) where
  hAppend := append

/-- Creates a vector from another with a provably equal length. -/
protected def cast {n m : Nat} (h : n = m) : Vector α n → Vector α m
  | ⟨x, p⟩ => ⟨x, h ▸ p⟩

/--
`extract v start halt` Returns the slice of `v` from indices `start` to `stop` (exclusive).
If `start` is greater or equal to `stop`, the result is empty.
If `stop` is greater than the size of `v`, the size is used instead.
-/
def extract (v : Vector α n) (start stop : Nat) : Vector α (min stop n - start) :=
  ⟨Array.extract v.toArray start stop, proof⟩
  where
    proof := by
      rw [size_extract, v.size_eq]

/-- Custom eliminator for `Vector α n` through Arrays -/
@[elab_as_elim]
def elimAsArray {motive : ∀ {n}, Vector α n → Sort u} (mk : ∀ a : Array α, motive ⟨a, rfl⟩) :
    {n : Nat} → (v : Vector α n) → motive v
  | _, ⟨a, rfl⟩ => mk a

/-- Custom eliminator for `Vector α n` throughLists -/
@[elab_as_elim]
def elimAsList {motive : ∀ {n}, Vector α n → Sort u} (mk : ∀ a : List α, motive ⟨⟨a⟩, rfl⟩) :
    {n : Nat} → (v : Vector α n) → motive v
  | _, ⟨⟨a⟩, rfl⟩ => mk a

/-- Maps a vector under a function. -/
def map (f : α → β) : Vector α n → Vector β n
  | ⟨a, h⟩ => ⟨Array.map f a, by simp [*]⟩

/-- Maps two vectors under a curried function of two variables. -/
def zipWith : Vector α n → Vector β n → (α → β → φ) → Vector φ n
  | ⟨a, h₁⟩, ⟨b, h₂⟩, f => ⟨Array.zipWith a b f, by simp [Array.size_zipWith, h₁, h₂]⟩

/-- Returns a vector of length `n` from a function on `Fin n`. -/
def ofFn (f : Fin n → α) : Vector α n := ⟨Array.ofFn f, by {rw [size_ofFn]}⟩

/--
Swaps two entries in a Vector.

This will perform the update destructively provided that `v` has a reference count of 1 when called.
-/
def swap (v : Vector α n) (i j : Fin n) : Vector α n :=
  ⟨Array.swap v.toArray (Fin.cast v.size_eq.symm i) (Fin.cast v.size_eq.symm j), proof⟩
  where
    proof := by
      rw [size_swap]
      exact v.size_eq

/--
`swapN v i j hi hj` swaps two `Nat` indexed entries in a `Vector α n`.
Uses `get_elem_tactic` to supply proofs `hi` and `hj` respectively
that the indices `i` and `j` are in range.

This will perform the update destructively provided that `v` has a reference count of 1 when called.
-/
def swapN (v : Vector α n) (i j : Nat)
    (hi : i < n := by get_elem_tactic) (hj : j < n := by get_elem_tactic) : Vector α n :=
  ⟨Array.swap v.toArray (Fin.cast v.size_eq.symm ⟨i, hi⟩) (Fin.cast v.size_eq.symm ⟨j, hj⟩),
    proof⟩
  where
    proof := by
      rw [size_swap]
      exact v.size_eq

/--
Swaps two entries in a `Vector α n`, or panics if either index is out of bounds.

This will perform the update destructively provided that `v` has a reference count of 1 when called.
-/
def swap! (v : Vector α n) (i j : Nat) : Vector α n :=
  ⟨Array.swap! v.toArray i j, by {rw [size_swap!]; exact v.size_eq}⟩

/--
Swaps the entry with index `i : Fin n` in the vector for a new entry.
The old entry is returned with the modified vector.
-/
def swapAt (v : Vector α n) (i : Fin n) (x : α) : α × Vector α n:=
  let res := v.toArray.swapAt (Fin.cast v.size_eq.symm i) x
  have proof : res.2.size = n := by
    simp only [swapAt_def, Fin.coe_cast, size_set, v.size_eq, res]
    done
  (res.1, ⟨res.2, proof⟩)

/--
Swaps the entry with index `i : Nat` in the vector for a new entry `x`.
The old entry is returned alongwith the modified vector.

Automatically generates proof of `i < n` with `get_elem_tactic` where feasible.
-/
def swapAtN (v : Vector α n) (i : Nat) (h : i < n := by get_elem_tactic) (x : α) : α × Vector α n :=
  swapAt v ⟨i,h⟩ x

/--
`swapAt! v i x` swaps out the entry at index `i : Nat` in the vector for `x`, if the index is valid.
Otherwise it panics The old entry is returned with the modified vector.
-/
def swapAt! (v : Vector α n) (i : Nat) (x : α) : α × Vector α n :=
  if h : i < n then
    swapAt v ⟨i, h⟩ x
  else
    have : Inhabited α := ⟨x⟩
    panic! s!"Index {i} is out of bounds"

/-- `range n` Returns a vector `#v[1,2,3,...,n-1]` -/
def range (n : Nat) : Vector Nat n :=
  ⟨Array.range n, by {simp}⟩

/-- Returns a vector of size `1` with a single element `v` -/
def singleton (v : α) : Vector α 1 :=
  mkVector 1 v

/-- Vector lookup function that takes an index `i` of type `USize` -/
def uget (v : Vector α n) (i : USize) (h : i.toNat < n) : α :=
  Array.uget v.toArray i (v.size_eq.symm ▸ h)

/-- `pop v` returns the vector with the last element removed -/
def pop (v : Vector α n) : Vector α (n-1) :=
  ⟨Array.pop v.toArray, by {rw [size_pop, v.size_eq]}⟩

/-- `shrink v m` shrinks the vector to the first `m` elements if `m < n`. -/
def shrink (v : Vector α n) (m : Nat) : Vector α (min m n) :=
  ⟨Array.shrink v.toArray m, proof⟩
  where
    proof := by
      rw [Array.shrink, Array.size_shrink_loop, v.size_eq]
      omega

/-- Drops `i` elements from a vector of length `n`; we can have `i > n`. -/
def drop (i : Nat) (v : Vector α n) : Vector α (n - i) :=
  have : min n n - i = n - i := by
    rw [Nat.min_self]
  Vector.cast this (extract v i n)

/-- Takes `i` elements from a vector of length `n`; we can have `i > n`. -/
alias take := shrink

/--
`isEqv` takes a given boolean property `p`. It returns `true`
if and only if `p a[i] b[i]` holds true for all valid indices `i`.
-/
def isEqv (a b : Vector α n) (p : α → α → Bool) : Bool :=
  Array.isEqv a.toArray b.toArray p

instance [BEq α] : BEq (Vector α n) :=
  ⟨fun a b => isEqv a b BEq.beq⟩

/-- `reverse v` reverses the vector `v` -/
def reverse (v : Vector α n) : Vector α n :=
  ⟨Array.reverse v.toArray, proof⟩
  where
    proof := by
      rw [size_reverse]
      exact v.size_eq

/--
`feraseIdx v i` removes the element at a given index from a vector using a Fin index.

This function takes worst case O(n) time because it has to backshift all elements
at positions greater than i.
-/
def feraseIdx (v : Vector α n) (i : Fin n) : Vector α (n-1) :=
  ⟨Array.feraseIdx v.toArray (Fin.cast v.size_eq.symm i), proof⟩
  where
    proof := by
      rw [Array.size_feraseIdx, v.size_eq]

/-- `Vector.tail` produces the tail of a vector -/
def tail (v : Vector α n)  : Vector α (n-1) :=
  match n with
  | 0 => v
  | _ + 1 => Vector.feraseIdx v 0

/--
`eraseIdx! v i` removes the element at position `i` from a vector of length `n` if `i < n`.
Panics otherwise.

This function takes worst case O(n) time because it has to backshift all elements at positions
greater than i.
-/
def eraseIdx! (v : Vector α n) (i : Nat) : Vector α (n-1) :=
  if h : i < n then
    feraseIdx v ⟨i,h⟩
  else
    have _ : Inhabited (Vector α (n-1)) := ⟨v.tail⟩
    panic! s!"Index {i} is out of bounds"

/--
`eraseIdxN v i h` removes the element at position `i` from a vector of length `n`.
`h : i < n` has a default argument `by get_elem_tactic` which tries to supply a proof
that the index is valid.

This function takes worst case O(n) time because it has to backshift all elements at positions
greater than i.
-/
def eraseIdxN (v : Vector α n) (i : Nat) (h : i < n := by get_elem_tactic) : Vector α (n - 1) :=
  v.feraseIdx ⟨i,h⟩

/--
If `x` is an element of vector `v` at index `j`, then `indexOf? v x` returns `some j`.
Otherwise it returns `none`.
-/
def indexOf? [BEq α] (v : Vector α n) (x : α) : Option (Fin n) :=
  match Array.indexOf? v.toArray x with
  | some res => some (Fin.cast v.size_eq res)
  | none => none

/-- `isPrefixOf as bs` returns true iff vector `as` is a prefix of vector`bs` -/
def isPrefixOf [BEq α] (as : Vector α m ) (bs : Vector α n) : Bool :=
  Array.isPrefixOf as.toArray bs.toArray

/-- `allDiff as i` returns `true` when all elements of `v` are distinct from each other` -/
def allDiff [BEq α] (as : Vector α n) : Bool :=
  Array.allDiff as.toArray

end Vector
